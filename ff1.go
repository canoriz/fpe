package fpe

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/subtle"
	"encoding/binary"
	"errors"
	"math"
	"math/big"
	"strings"
)

// Note that this is strictly following the official NIST spec guidelines.
// In the linked PDF Appendix A (README.md), NIST recommends that radix^minLength >= 1,000,000.
// If you would like to follow that, change this parameter.
const (
	feistelMin       = 100
	feistelMinStrict = 1_000_000
	numRounds        = 10
	blockSize        = aes.BlockSize
	halfBlockSize    = blockSize / 2
	// maxRadix   = 65536 // 2^16
)

var (
	// ErrStringNotInRadix is returned if input or intermediate strings cannot be parsed in the given radix
	ErrStringNotInRadix = errors.New("string is not within base/radix")

	// ErrTweakLengthInvalid is returned if the tweak length is not in the given range
	ErrTweakLengthInvalid = errors.New("tweak must be between 0 and given maxTLen, inclusive")
)

// A Cipher is an instance of the FF1 mode of format preserving encryption
// using a particular key, radix, and tweak
type Cipher struct {
	tweak  []byte
	radix  int
	minLen uint32
	maxLen uint32

	aesBlock cipher.Block
}

// NewCipher initializes a new FF1 Cipher for encryption or decryption use
// based on the radix, max tweak length, key and tweak parameters.
func NewCipher(
	radix int, maxTLen int, key []byte, tweak []byte, strict bool,
) (Cipher, error) {
	var newCipher Cipher

	keyLen := len(key)

	// Check if the key is 128, 192, or 256 bits = 16, 24, or 32 bytes
	if (keyLen != 16) && (keyLen != 24) && (keyLen != 32) {
		return newCipher, errors.New("key length must be 128, 192, or 256 bits")
	}

	// While FF1 allows radices in [2, 2^16],
	// realistically there's a practical limit based on the alphabet that can be passed in
	if (radix < 2) || (radix > big.MaxBase) {
		return newCipher, errors.New("radix must be between 2 and big.MaxBase, inclusive")
	}

	// Calculate minLength
	minLen := uint32(math.MaxUint32)
	if strict {
		minLen = uint32(math.Ceil(math.Log(feistelMinStrict) / math.Log(float64(radix))))
	} else {
		minLen = uint32(math.Ceil(math.Log(feistelMin) / math.Log(float64(radix))))
	}

	var maxLen uint32 = math.MaxUint32

	// Make sure 2 <= minLength <= maxLength < 2^32 is satisfied
	if (minLen < 2) || (maxLen < minLen) {
		return newCipher, errors.New("minLen invalid, adjust your radix")
	}

	// aes.NewCipher automatically returns the correct block based on the length of the key passed in
	aesBlock, err := aes.NewCipher(key)
	if err != nil {
		return newCipher, errors.New("failed to create AES block")
	}

	newCipher.tweak = tweak
	newCipher.radix = radix
	newCipher.minLen = minLen
	newCipher.maxLen = maxLen
	newCipher.aesBlock = aesBlock

	return newCipher, nil
}

// Encrypt encrypts the string X over the current FF1 parameters
// and returns the ciphertext of the same length and format
func (c Cipher) Encrypt(X string) (string, error) {
	return c.EncryptWithTweak(X, c.tweak)
}

// EncryptWithTweak is the same as Encrypt except it uses the
// tweak from the parameter rather than the current Cipher's tweak
// This allows you to re-use a single Cipher (for a given key) and simply
// override the tweak for each unique data input, which is a practical
// use-case of FPE for things like credit card numbers.
func (c Cipher) EncryptWithTweak(X string, tweak []byte) (string, error) {
	var ret string
	var ok bool

	n := uint32(len(X))
	t := len(tweak)

	// Check if message length is within minLength and maxLength bounds
	if (n < c.minLen) || (n > c.maxLen) {
		return ret, errors.New("message length is not within min and max bounds")
	}

	radix := c.radix

	// Check if the message is in the current radix
	var numX big.Int
	_, ok = numX.SetString(X, radix)
	if !ok {
		return ret, ErrStringNotInRadix
	}

	// Calculate split point
	u := n / 2
	v := n - u

	// Split the message
	A := X[:u]
	B := X[u:]

	// Byte lengths
	var b int
	var d int
	{
		// TODO: constant time and optimize of bitlen
		var bb, vv big.Int
		bb.SetInt64(int64(radix))
		vv.Exp(&bb, big.NewInt(int64(v)), nil)
		vv.Sub(&vv, big.NewInt(1))
		b = (vv.BitLen() + 7) / 8
		d = 4*((b+3)/4) + 4
	}

	// Calculate P, doesn't change in each loop iteration
	// P's length is always 16, so it can stay on the stack, separate from buf
	const lenP = blockSize
	// Q's length is known to always be t+b+1+numPad, to be multiple of 16
	lenQ := (t + b + 1 + 15) / 16 * 16
	numPad := lenQ - (t + b + 1)
	// For a given input X, the size of PQ is deterministic: 16+lenQ
	lenPQ := lenP + lenQ

	// bigBuf: P, Q, S: (d+15/16)*16 bytes
	// S will take at most d bytes, and ceiling to 16 bytes block
	// S's first 16-byte block is shared with R
	bigBuf := make([]byte, lenPQ+((d+15)/16)*16)
	PQ := bigBuf[:lenPQ]
	S := bigBuf[lenPQ:]

	PQ[0] = 0x01
	PQ[1] = 0x02
	PQ[2] = 0x01

	// radix must fill 3 bytes, so pad 1 zero byte
	PQ[3] = 0x00
	binary.BigEndian.PutUint16(PQ[4:6], uint16(radix))

	PQ[6] = 0x0a
	PQ[7] = byte(u) // overflow automatically does the modulus

	binary.BigEndian.PutUint32(PQ[8:12], n)
	binary.BigEndian.PutUint32(PQ[12:lenP], uint32(t))

	Q := PQ[lenP:]
	copy(Q[:t], tweak)
	// These are re-used in the for loop below
	// variables names prefixed with "num" indicate big integers
	var (
		numA, numB       big.Int
		numRadix, numY   big.Int
		numU, numV       big.Int
		numModU, numModV big.Int
	)

	{
		numB.SetString(B, radix)
		if !ok {
			return ret, ErrStringNotInRadix
		}
		numA.SetString(A, radix)
		if !ok {
			return ret, ErrStringNotInRadix
		}
		numRadix.SetInt64(int64(radix))

		// Pre-calculate the modulus since it's only one of 2 values,
		// depending on whether i is even or odd
		numU.SetInt64(int64(u))
		numV.SetInt64(int64(v))

		numModU.Exp(&numRadix, &numU, nil)
		numModV.Exp(&numRadix, &numV, nil)
	}

	for i := 0; i < numRounds; i++ {
		// 6i
		Q[t+numPad] = byte(i)
		numB.FillBytes(Q[t+numPad+1:])

		// 6ii
		R, err := c.prf(PQ, S)
		if err != nil {
			return ret, err
		}

		// 6iii
		for j := 16; j < d; j += 16 {
			xorBlock := S[j : j+16]
			for k := 0; k < 8; k++ {
				xorBlock[k] = 0
			}
			binary.BigEndian.PutUint64(xorBlock[8:], uint64(j/16))
			subtle.XORBytes(xorBlock, xorBlock, R)

			// AES encrypt the current xored block
			_, err = c.blockCiph(xorBlock, xorBlock)
			if err != nil {
				return ret, err
			}
		}

		// 6iv
		numY.SetBytes(S[:d])

		// 6v,6vi
		numA.Add(&numA, &numY)
		if i%2 == 0 {
			numA.Mod(&numA, &numModU)
		} else {
			numA.Mod(&numA, &numModV)
		}

		// 6viii 6ix
		// big.Ints use pointers behind the scenes so when numB gets updated,
		// numA will transparently get updated to it. Hence, set the bytes explicitly
		numTmp := numA
		numA = numB
		numB = numTmp
	}

	A = numA.Text(radix)
	B = numB.Text(radix)

	// Pad both A and B properly
	A = strings.Repeat("0", int(u)-len(A)) + A
	B = strings.Repeat("0", int(v)-len(B)) + B

	ret = A + B

	return ret, nil
}

// Decrypt decrypts the string X over the current FF1 parameters
// and returns the plaintext of the same length and format
func (c Cipher) Decrypt(X string) (string, error) {
	return c.DecryptWithTweak(X, c.tweak)
}

// DecryptWithTweak is the same as Decrypt except it uses the
// tweak from the parameter rather than the current Cipher's tweak
// This allows you to re-use a single Cipher (for a given key) and simply
// override the tweak for each unique data input, which is a practical
// use-case of FPE for things like credit card numbers.
func (c Cipher) DecryptWithTweak(X string, tweak []byte) (string, error) {
	var ret string
	var ok bool

	n := uint32(len(X))
	t := len(tweak)

	// Check if message length is within minLength and maxLength bounds
	if (n < c.minLen) || (n > c.maxLen) {
		return ret, errors.New("message length is not within min and max bounds")
	}

	radix := c.radix

	// Check if the message is in the current radix
	var numX big.Int
	_, ok = numX.SetString(X, radix)
	if !ok {
		return ret, ErrStringNotInRadix
	}

	// Calculate split point
	u := n / 2
	v := n - u

	// Split the message
	A := X[:u]
	B := X[u:]

	// Byte lengths
	var b int
	var d int
	{
		// TODO: constant time and optimize of bitlen
		var bb, vv big.Int
		bb.SetInt64(int64(radix))
		vv.Exp(&bb, big.NewInt(int64(v)), nil)
		vv.Sub(&vv, big.NewInt(1))
		b = (vv.BitLen() + 7) / 8
		d = 4*((b+3)/4) + 4
	}

	// Calculate P, doesn't change in each loop iteration
	// P's length is always 16, so it can stay on the stack, separate from buf
	const lenP = blockSize
	// Q's length is known to always be t+b+1+numPad, to be multiple of 16
	lenQ := (t + b + 1 + 15) / 16 * 16
	numPad := lenQ - (t + b + 1)
	// For a given input X, the size of PQ is deterministic: 16+lenQ
	lenPQ := lenP + lenQ

	// bigBuf: P, Q, S: (d+15/16)*16 bytes
	// S will take at most d bytes, and ceiling to 16 bytes block
	// S's first 16-byte block is shared with R
	bigBuf := make([]byte, lenPQ+((d+15)/16)*16)
	PQ := bigBuf[:lenPQ]
	S := bigBuf[lenPQ:]

	PQ[0] = 0x01
	PQ[1] = 0x02
	PQ[2] = 0x01

	// radix must fill 3 bytes, so pad 1 zero byte
	PQ[3] = 0x00
	binary.BigEndian.PutUint16(PQ[4:6], uint16(radix))

	PQ[6] = 0x0a
	PQ[7] = byte(u) // overflow automatically does the modulus

	binary.BigEndian.PutUint32(PQ[8:12], n)
	binary.BigEndian.PutUint32(PQ[12:lenP], uint32(t))

	Q := PQ[lenP:]
	copy(Q[:t], tweak)
	// These are re-used in the for loop below
	// variables names prefixed with "num" indicate big integers
	var (
		numA, numB       big.Int
		numRadix, numY   big.Int
		numU, numV       big.Int
		numModU, numModV big.Int
	)

	{
		numB.SetString(B, radix)
		if !ok {
			return ret, ErrStringNotInRadix
		}
		numA.SetString(A, radix)
		if !ok {
			return ret, ErrStringNotInRadix
		}
		numRadix.SetInt64(int64(radix))

		// Pre-calculate the modulus since it's only one of 2 values,
		// depending on whether i is even or odd
		numU.SetInt64(int64(u))
		numV.SetInt64(int64(v))

		numModU.Exp(&numRadix, &numU, nil)
		numModV.Exp(&numRadix, &numV, nil)
	}

	for i := numRounds - 1; i >= 0; i-- {
		// 6i
		Q[t+numPad] = byte(i)
		numA.FillBytes(Q[t+numPad+1:])

		// 6ii
		R, err := c.prf(PQ, S)
		if err != nil {
			return ret, err
		}

		// 6iii
		for j := 16; j < d; j += 16 {
			xorBlock := S[j : j+16]
			for k := 0; k < 8; k++ {
				xorBlock[k] = 0
			}
			binary.BigEndian.PutUint64(xorBlock[8:], uint64(j/16))
			subtle.XORBytes(xorBlock, xorBlock, R)

			// AES encrypt the current xored block
			_, err = c.blockCiph(xorBlock, xorBlock)
			if err != nil {
				return ret, err
			}
		}

		// 6iv
		numY.SetBytes(S[:d])

		// 6v,6vi
		numB.Sub(&numB, &numY)
		if i%2 == 0 {
			numB.Mod(&numB, &numModU)
		} else {
			numB.Mod(&numB, &numModV)
		}

		// 6viii 6ix
		// big.Ints use pointers behind the scenes so when numB gets updated,
		// numA will transparently get updated to it. Hence, set the bytes explicitly
		numTmp := numB
		numB = numA
		numA = numTmp
	}

	A = numA.Text(radix)
	B = numB.Text(radix)

	// Pad both A and B properly
	A = strings.Repeat("0", int(u)-len(A)) + A
	B = strings.Repeat("0", int(v)-len(B)) + B

	ret = A + B

	return ret, nil
}

// blockCiph defines how the main block cipher is called.
// It is guaranteed to be a single-block (16-byte) input because that's what the
// algorithm dictates.
func (c Cipher) blockCiph(input []byte, dst []byte) ([]byte, error) {
	// These are checked here manually because the CryptBlocks function panics rather than returning an error
	// So, catch the potential error earlier
	if len(input)%blockSize != 0 {
		return nil, errors.New("length of ciph input must be multiple of 16")
	}

	c.aesBlock.Encrypt(dst, input)

	return dst[:len(input)], nil
}

// PRF as defined in the NIST spec is actually just AES-CBC,
// which is the last block of an AES-CBC encrypted ciphertext.
// Utilize the blockCiph function for the AES-CBC.
// PRF always outputs 16 bytes (one block)
func (c Cipher) prf(src []byte, dst []byte) ([]byte, error) {
	// These are checked here manually because the CryptBlocks function panics rather than returning an error
	// So, catch the potential error earlier
	if len(src)%blockSize != 0 {
		return nil, errors.New("prf: length of ciph input must be multiple of 16")
	}
	if len(dst) < blockSize {
		return nil, errors.New("prf: output smaller than 16")
	}

	// iv is always 0
	// use dst as iv
	for i := 0; i < 16; i++ {
		dst[i] = 0x00
	}

	// Below is modified from Go std's cbc.
	// We only need CBC's last block, so dst offset is not move forward
	for len(src) > 0 {
		// Write the xor to dst, then encrypt in place.
		subtle.XORBytes(dst[:blockSize], src[:blockSize], dst[:blockSize])
		c.aesBlock.Encrypt(dst[:blockSize], dst[:blockSize])

		// Move to the next block with this block as the next iv.
		src = src[blockSize:]
	}
	return dst[:blockSize], nil
}
