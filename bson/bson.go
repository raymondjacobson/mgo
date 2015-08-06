// BSON library for Go
//
// Copyright (c) 2010-2012 - Gustavo Niemeyer <gustavo@niemeyer.net>
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this
//    list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice,
//    this list of conditions and the following disclaimer in the documentation
//    and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
// ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// Package bson is an implementation of the BSON specification for Go:
//
//     http://bsonspec.org
//
// It was created as part of the mgo MongoDB driver for Go, but is standalone
// and may be used on its own without the driver.
package bson

import (
	"bytes"
	"crypto/md5"
	"crypto/rand"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"reflect"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode"
)

// --------------------------------------------------------------------------
// The public API.

// A value implementing the bson.Getter interface will have its GetBSON
// method called when the given value has to be marshalled, and the result
// of this method will be marshaled in place of the actual object.
//
// If GetBSON returns return a non-nil error, the marshalling procedure
// will stop and error out with the provided value.
type Getter interface {
	GetBSON() (interface{}, error)
}

// A value implementing the bson.Setter interface will receive the BSON
// value via the SetBSON method during unmarshaling, and the object
// itself will not be changed as usual.
//
// If setting the value works, the method should return nil or alternatively
// bson.SetZero to set the respective field to its zero value (nil for
// pointer types). If SetBSON returns a value of type bson.TypeError, the
// BSON value will be omitted from a map or slice being decoded and the
// unmarshalling will continue. If it returns any other non-nil error, the
// unmarshalling procedure will stop and error out with the provided value.
//
// This interface is generally useful in pointer receivers, since the method
// will want to change the receiver. A type field that implements the Setter
// interface doesn't have to be a pointer, though.
//
// Unlike the usual behavior, unmarshalling onto a value that implements a
// Setter interface will NOT reset the value to its zero state. This allows
// the value to decide by itself how to be unmarshalled.
//
// For example:
//
//     type MyString string
//
//     func (s *MyString) SetBSON(raw bson.Raw) error {
//         return raw.Unmarshal(s)
//     }
//
type Setter interface {
	SetBSON(raw Raw) error
}

// SetZero may be returned from a SetBSON method to have the value set to
// its respective zero value. When used in pointer values, this will set the
// field to nil rather than to the pre-allocated value.
var SetZero = errors.New("set to zero")

// M is a convenient alias for a map[string]interface{} map, useful for
// dealing with BSON in a native way.  For instance:
//
//     bson.M{"a": 1, "b": true}
//
// There's no special handling for this type in addition to what's done anyway
// for an equivalent map type.  Elements in the map will be dumped in an
// undefined ordered. See also the bson.D type for an ordered alternative.
type M map[string]interface{}

// D represents a BSON document containing ordered elements. For example:
//
//     bson.D{{"a", 1}, {"b", true}}
//
// In some situations, such as when creating indexes for MongoDB, the order in
// which the elements are defined is important.  If the order is not important,
// using a map is generally more comfortable. See bson.M and bson.RawD.
type D []DocElem

// DocElem is an element of the bson.D document representation.
type DocElem struct {
	Name  string
	Value interface{}
}

// Map returns a map out of the ordered element name/value pairs in d.
func (d D) Map() (m M) {
	m = make(M, len(d))
	for _, item := range d {
		m[item.Name] = item.Value
	}
	return m
}

// The Raw type represents raw unprocessed BSON documents and elements.
// Kind is the kind of element as defined per the BSON specification, and
// Data is the raw unprocessed data for the respective element.
// Using this type it is possible to unmarshal or marshal values partially.
//
// Relevant documentation:
//
//     http://bsonspec.org/#/specification
//
type Raw struct {
	Kind byte
	Data []byte
}

// RawD represents a BSON document containing raw unprocessed elements.
// This low-level representation may be useful when lazily processing
// documents of uncertain content, or when manipulating the raw content
// documents in general.
type RawD []RawDocElem

// See the RawD type.
type RawDocElem struct {
	Name  string
	Value Raw
}

// ObjectId is a unique ID identifying a BSON value. It must be exactly 12 bytes
// long. MongoDB objects by default have such a property set in their "_id"
// property.
//
// http://www.mongodb.org/display/DOCS/Object+IDs
type ObjectId string

// ObjectIdHex returns an ObjectId from the provided hex representation.
// Calling this function with an invalid hex representation will
// cause a runtime panic. See the IsObjectIdHex function.
func ObjectIdHex(s string) ObjectId {
	d, err := hex.DecodeString(s)
	if err != nil || len(d) != 12 {
		panic(fmt.Sprintf("Invalid input to ObjectIdHex: %q", s))
	}
	return ObjectId(d)
}

// IsObjectIdHex returns whether s is a valid hex representation of
// an ObjectId. See the ObjectIdHex function.
func IsObjectIdHex(s string) bool {
	if len(s) != 24 {
		return false
	}
	_, err := hex.DecodeString(s)
	return err == nil
}

// objectIdCounter is atomically incremented when generating a new ObjectId
// using NewObjectId() function. It's used as a counter part of an id.
var objectIdCounter uint32 = 0

// machineId stores machine id generated once and used in subsequent calls
// to NewObjectId function.
var machineId = readMachineId()

// readMachineId generates machine id and puts it into the machineId global
// variable. If this function fails to get the hostname, it will cause
// a runtime error.
func readMachineId() []byte {
	var sum [3]byte
	id := sum[:]
	hostname, err1 := os.Hostname()
	if err1 != nil {
		_, err2 := io.ReadFull(rand.Reader, id)
		if err2 != nil {
			panic(fmt.Errorf("cannot get hostname: %v; %v", err1, err2))
		}
		return id
	}
	hw := md5.New()
	hw.Write([]byte(hostname))
	copy(id, hw.Sum(nil))
	return id
}

// NewObjectId returns a new unique ObjectId.
func NewObjectId() ObjectId {
	var b [12]byte
	// Timestamp, 4 bytes, big endian
	binary.BigEndian.PutUint32(b[:], uint32(time.Now().Unix()))
	// Machine, first 3 bytes of md5(hostname)
	b[4] = machineId[0]
	b[5] = machineId[1]
	b[6] = machineId[2]
	// Pid, 2 bytes, specs don't specify endianness, but we use big endian.
	pid := os.Getpid()
	b[7] = byte(pid >> 8)
	b[8] = byte(pid)
	// Increment, 3 bytes, big endian
	i := atomic.AddUint32(&objectIdCounter, 1)
	b[9] = byte(i >> 16)
	b[10] = byte(i >> 8)
	b[11] = byte(i)
	return ObjectId(b[:])
}

// NewObjectIdWithTime returns a dummy ObjectId with the timestamp part filled
// with the provided number of seconds from epoch UTC, and all other parts
// filled with zeroes. It's not safe to insert a document with an id generated
// by this method, it is useful only for queries to find documents with ids
// generated before or after the specified timestamp.
func NewObjectIdWithTime(t time.Time) ObjectId {
	var b [12]byte
	binary.BigEndian.PutUint32(b[:4], uint32(t.Unix()))
	return ObjectId(string(b[:]))
}

// String returns a hex string representation of the id.
// Example: ObjectIdHex("4d88e15b60f486e428412dc9").
func (id ObjectId) String() string {
	return fmt.Sprintf(`ObjectIdHex("%x")`, string(id))
}

// Hex returns a hex representation of the ObjectId.
func (id ObjectId) Hex() string {
	return hex.EncodeToString([]byte(id))
}

// MarshalJSON turns a bson.ObjectId into a json.Marshaller.
func (id ObjectId) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf(`"%x"`, string(id))), nil
}

var nullBytes = []byte("null")

// UnmarshalJSON turns *bson.ObjectId into a json.Unmarshaller.
func (id *ObjectId) UnmarshalJSON(data []byte) error {
	if len(data) == 2 && data[0] == '"' && data[1] == '"' || bytes.Equal(data, nullBytes) {
		*id = ""
		return nil
	}
	if len(data) != 26 || data[0] != '"' || data[25] != '"' {
		return errors.New(fmt.Sprintf("Invalid ObjectId in JSON: %s", string(data)))
	}
	var buf [12]byte
	_, err := hex.Decode(buf[:], data[1:25])
	if err != nil {
		return errors.New(fmt.Sprintf("Invalid ObjectId in JSON: %s (%s)", string(data), err))
	}
	*id = ObjectId(string(buf[:]))
	return nil
}

// Valid returns true if id is valid. A valid id must contain exactly 12 bytes.
func (id ObjectId) Valid() bool {
	return len(id) == 12
}

// byteSlice returns byte slice of id from start to end.
// Calling this function with an invalid id will cause a runtime panic.
func (id ObjectId) byteSlice(start, end int) []byte {
	if len(id) != 12 {
		panic(fmt.Sprintf("Invalid ObjectId: %q", string(id)))
	}
	return []byte(string(id)[start:end])
}

// Time returns the timestamp part of the id.
// It's a runtime error to call this method with an invalid id.
func (id ObjectId) Time() time.Time {
	// First 4 bytes of ObjectId is 32-bit big-endian seconds from epoch.
	secs := int64(binary.BigEndian.Uint32(id.byteSlice(0, 4)))
	return time.Unix(secs, 0)
}

// Machine returns the 3-byte machine id part of the id.
// It's a runtime error to call this method with an invalid id.
func (id ObjectId) Machine() []byte {
	return id.byteSlice(4, 7)
}

// Pid returns the process id part of the id.
// It's a runtime error to call this method with an invalid id.
func (id ObjectId) Pid() uint16 {
	return binary.BigEndian.Uint16(id.byteSlice(7, 9))
}

// Counter returns the incrementing value part of the id.
// It's a runtime error to call this method with an invalid id.
func (id ObjectId) Counter() int32 {
	b := id.byteSlice(9, 12)
	// Counter is stored as big-endian 3-byte value
	return int32(uint32(b[0])<<16 | uint32(b[1])<<8 | uint32(b[2]))
}

// The Symbol type is similar to a string and is used in languages with a
// distinct symbol type.
type Symbol string

// Now returns the current time with millisecond precision. MongoDB stores
// timestamps with the same precision, so a Time returned from this method
// will not change after a roundtrip to the database. That's the only reason
// why this function exists. Using the time.Now function also works fine
// otherwise.
func Now() time.Time {
	return time.Unix(0, time.Now().UnixNano()/1e6*1e6)
}

// MongoTimestamp is a special internal type used by MongoDB that for some
// strange reason has its own datatype defined in BSON.
type MongoTimestamp int64

type orderKey int64

// MaxKey is a special value that compares higher than all other possible BSON
// values in a MongoDB database.
var MaxKey = orderKey(1<<63 - 1)

// MinKey is a special value that compares lower than all other possible BSON
// values in a MongoDB database.
var MinKey = orderKey(-1 << 63)

type undefined struct{}

// Undefined represents the undefined BSON value.
var Undefined undefined

// Binary is a representation for non-standard binary values.  Any kind should
// work, but the following are known as of this writing:
//
//   0x00 - Generic. This is decoded as []byte(data), not Binary{0x00, data}.
//   0x01 - Function (!?)
//   0x02 - Obsolete generic.
//   0x03 - UUID
//   0x05 - MD5
//   0x80 - User defined.
//
type Binary struct {
	Kind byte
	Data []byte
}

// RegEx represents a regular expression.  The Options field may contain
// individual characters defining the way in which the pattern should be
// applied, and must be sorted. Valid options as of this writing are 'i' for
// case insensitive matching, 'm' for multi-line matching, 'x' for verbose
// mode, 'l' to make \w, \W, and similar be locale-dependent, 's' for dot-all
// mode (a '.' matches everything), and 'u' to make \w, \W, and similar match
// unicode. The value of the Options parameter is not verified before being
// marshaled into the BSON format.
type RegEx struct {
	Pattern string
	Options string
}

// JavaScript is a type that holds JavaScript code. If Scope is non-nil, it
// will be marshaled as a mapping from identifiers to values that may be
// used when evaluating the provided Code.
type JavaScript struct {
	Code  string
	Scope interface{}
}

// DBPointer refers to a document id in a namespace.
//
// This type is deprecated in the BSON specification and should not be used
// except for backwards compatibility with ancient applications.
type DBPointer struct {
	Namespace string
	Id        ObjectId
}

// BSONuint128_32 is a struct that represents a 128 bit integer and is used
// internally for ToString and MakeDec128 methods for the Dec128 BSON type.
type BSONuint128_32 struct {
	// Stored as four 32 bit words high to low
	parts [4]uint32
}

// This function divides a BSONuint128_32 by 1000000000 (1 billion) and
// computes the quotient and remainder
func (value BSONuint128_32) Divide1B() (BSONuint128_32, uint32) {
	var quotient BSONuint128_32
	var remainder uint64 = 0
	var divisor uint32 = 1000 * 1000 * 1000

	if value.parts[0] == 0 && value.parts[1] == 0 &&
	   value.parts[2] == 0 && value.parts[3] == 0 {
		quotient = value
		return quotient, uint32(remainder)
	}

	for i := 0; i <= 3; i++ {
		// Adjust remainder to match value of next dividend
		remainder <<= 32
		// Add the dividend to remainder
		remainder += uint64(value.parts[i])
		quotient.parts[i] = uint32(remainder / uint64(divisor))
		remainder %= uint64(divisor)
	}

	return quotient, uint32(remainder)
}

// BSONuint128_64 is a struct that represents a 128 bit integer and is used
// internally for the MakeDec128 method for the Dec128 BSON type.
type BSONuint128_64 struct {
	High uint64
	Low uint64
}

// This function multiplies two uint64's to get a BSONuint128_64
func Multiply64x64(left uint64, right uint64) BSONuint128_64 {
	if left == 0 && right == 0 {
		return BSONuint128_64{0, 0}
	}
	var leftHigh uint64 = left >> 32
	var leftLow uint64 = uint64(uint32(left))
	var rightHigh uint64 = right >> 32
	var rightLow uint64 = uint64(uint32(right))

	var productHigh uint64 = leftHigh * rightHigh
	var productMidl uint64 = leftHigh * rightLow
	var productMidr uint64 = leftLow * rightHigh
	var productLow uint64 = leftLow * rightLow

	productHigh += (productMidl >> 32)
	productMidl = uint64(uint32(productMidl)) + productMidr + (productLow >> 32)

	productHigh += (productMidl >> 32)
	productLow = (productMidl << 32) + uint64(uint32(productLow))

	return BSONuint128_64{productHigh, productLow}
}

// Dec128 refers to the BSON type for the 128-bit IEEE 754-2008 decimal.
type Dec128 struct {
	Low64  uint64
	High64 uint64
}

func (dec Dec128) IsNaN() bool {
	return dec.High64 == 0x7c00000000000000
}

func (dec Dec128) IsPositiveInfinity() bool {
	return dec.High64 == 0x7800000000000000
}

func (dec Dec128) IsNegativeInfinity() bool {
	return dec.High64 == 0xf800000000000000
}

func (dec Dec128) IsIdentical(other Dec128) bool {
	return (dec.High64 == other.High64) && (dec.Low64 == other.Low64)
}

func (dec Dec128) ToString() string {
	var combinationMask uint32 = 0x1f    // Extract least significant 5 bits
	var exponentMask uint32 = 0x3fff     // Extract least significant 14 bits
	var combinationInfinity uint32 = 30  // Value of combination field for Inf
	var combinationNaN uint32 = 31		 // Value of combination field for NaN
	var exponentBias uint32 = 6176       // decimal128 exponent bias

	var outStr string = ""

	var low uint32 = uint32(dec.Low64)			 // Bits 0 - 31
	var midl uint32 = uint32(dec.Low64 >> 32)    // Bits 32 - 63
	var midh uint32 = uint32(dec.High64)         // Bits 64 - 95
	var high uint32 = uint32(dec.High64 >> 32)   // Bits 96 - 107
	var combination uint32				 // Bits 1 - 5
	var biasedExponent uint32			 // Decoded 14 bit biased exponent
	var significandDigits uint32 = 0     // Number of significand digits
	var significand [36]uint32           // Base 10 digits in significand
	var exponent int32					 // Unbiased exponent
	var isZero bool 					 // True if the number is zero
	var significandMSB uint8			 // Most significant bits (50 - 46)

	// dec is negative
	if int64(dec.High64) < 0 {
		outStr += "-"
	}

	// Decode combination field and exponent
	combination = (high >> 26) & combinationMask

	if (combination >> 3) == 3 {
		// Check for special values
		if combination == combinationInfinity {
			outStr += "Infinity"
			return outStr
		} else if combination == combinationNaN {
			// Drop the sign, +NaN and -NaN behave the same in MongoDB
			outStr = "NaN"
			return outStr
		} else {
			biasedExponent = (high >> 15) & exponentMask
			significandMSB = uint8(0x8 + (high >> 14) & 0x01)
		}
	} else {
		biasedExponent = (high >> 17) & exponentMask
		significandMSB = uint8(high >> 14) & 0x7
	}

	exponent = int32(biasedExponent - exponentBias)

	// Convert 114 bit binary number in the significand to at most
	// 34 decimal digits using modulo and division.
	var significand128 = BSONuint128_32{[4]uint32{
		(high & exponentMask) + (uint32(significandMSB & 0xf) << 14),
		midh,
		midl,
		low,
	}}

	if significand128.parts[0] == 0 && significand128.parts[1] == 0 &&
	   significand128.parts[2] == 0 && significand128.parts[3] == 0 {
	   	isZero = true
	} else {
		var leastDigits uint32
		for k := 3; k >= 0; k-- {
			significand128, leastDigits = significand128.Divide1B()

			// We now have the 9 least significand digits (in base 2).
			// Convert and output to a string
			if leastDigits == 0 {
				continue
			}

			for j := 8; j >= 0; j-- {
				significand[k * 9 + j] = leastDigits % 10
				leastDigits /= 10
			}
		}
	}

	// Output format options
	// Scientific : [-]d.dddE(+/-)dd or [-]dE(+/-)dd
	// Regular    : ddd.ddd
	var significandRead uint32 = 0
	if isZero {
		significandDigits = 1
		significandRead = 0
	} else {
		significandDigits = 36
		// Move significandRead to where the significand is not led with zeros
		for significandRead < 35 && significand[significandRead] == 0 {
			significandDigits--
			significandRead++
		}
	}
	var scientificExponent int32 = int32(significandDigits) - 1 + exponent

	if scientificExponent >= 12 || scientificExponent <= -4 ||
	   exponent > 0 || (isZero && scientificExponent != 0) {
		// Scientific format
		outStr += string(significand[significandRead] + '0')
		significandRead++
		significandDigits--

		if significandDigits != 0 {
			outStr += "."
		}

		for i := uint32(0); i < significandDigits; i++ {
			outStr += string(significand[significandRead] + '0')
			significandRead++
		}
		// Exponent
		outStr += "E"
		if scientificExponent > 0 {
			outStr += "+"
		}
		outStr += strconv.Itoa(int(scientificExponent))
	} else {
		// Regular format
		if exponent >= 0 {
			for i := uint32(0); i < significandDigits; i++ {
				outStr += string(significand[significandRead] + '0')
				significandRead++
			}
		} else {
			var radixPosition int32 = int32(significandDigits) + exponent
			if radixPosition > 0 {
				// If we have non-zero digits before the radix
				for i := int32(0); i< radixPosition; i++ {
					outStr += string(significand[significandRead] + '0')
					significandRead++
				}
			} else {
				// Add a leading zero before radix point
				outStr += "0"
			}

			outStr += "."
			for radixPosition < 0 {
				// Add leading zeros after radix point
				outStr += "0"
				radixPosition++
			}
			var maxRadixPosition uint32 = 0
			if radixPosition - 1 > 0 {
				maxRadixPosition = uint32(radixPosition - 1)
			}
			for i := uint32(0); i < significandDigits - maxRadixPosition; i++ {
				outStr += string(significand[significandRead] + '0')
				if significandRead >= uint32(len(significand) - 1) {
					break
				}
				significandRead++
			}
		}
	}

	return outStr
}

func MakeDec128Infinity(negative bool) Dec128 {
	if !negative {
		return Dec128{0, 0x7800000000000000}
	}
	return Dec128{0, 0xf800000000000000}
}

func MakeDec128NaN() Dec128 {
	return Dec128{0, 0x7c00000000000000}
}

func MakeDec128(str string) Dec128 {
	// State tracking
	var isNegative bool = false
	var sawRadix bool = false
	var foundNonZero bool = false

	var nDigitsNoTrailing uint16 = 0 // Total number of sig. digits (no trailing zeros)
	var nDigitsRead uint16 = 0	  	 // Total number of significand digits read
	var nDigits uint16 = 0		  	 // Total number of sig. digits
	var radixPosition uint16 = 0  	 // The number of digits after the radix point
	var firstNonZero uint16 = 0	  	 // The index of the first non zero

	const BSONDec128MaxDigits int = 34
	const BSONDec128ExponentMax int = 6111
	const BSONDec128ExponentBias int = 6176
	const BSONDec128ExponentMin int = -6176
	var digits [BSONDec128MaxDigits]uint16
	var digitsInsertPosition int = 0
	var nDigitsStored uint16 = 0
	var firstDigit uint16 = 0		 // The index of the first digit
	var lastDigit uint16 = 0		 // The index of the last digit

	var exponent int32 = 0

	var strRead = 0
	var strLen = len(str)

	// Strip off whitespace
	str = strings.TrimSpace(str)

	// Check for empty string
	if strLen == 0 {
		return MakeDec128NaN()
	}

	// Check sign
	if str[strRead] == '+' || str[strRead] == '-' {
		isNegative = (str[strRead] == '-')
		strRead++
	}

	if (strRead >= strLen) {
		return MakeDec128NaN()
	}

	// Check for Infinity and NaN
	if unicode.IsLetter(rune(str[strRead])) || !unicode.IsDigit(rune(str[strRead])) ||
	   str[strRead] == '.' {
		if str[strRead] == 'i' || str[strRead] == 'I' {
			strRead++
			if strRead >= strLen {
				return MakeDec128NaN()
			}
			if str[strRead] == 'n' || str[strRead] == 'N' {
				strRead++
				if strRead >= strLen {
					return MakeDec128NaN()
				}
				if str[strRead] == 'f' || str[strRead] == 'F' {
					return MakeDec128Infinity(isNegative)
				}
			}
		}

		return MakeDec128NaN()
	}

	// Read digits
	for (unicode.IsDigit(rune(str[strRead])) || str[strRead] == '.') {
		if str[strRead] == '.' {
			if sawRadix {
				return MakeDec128NaN()
			}

			sawRadix = true
			if strRead < strLen - 1 {
				strRead++
			} else {
				break
			}
			continue
		}

		if nDigitsStored < 34 {
			if str[strRead] != '0' || foundNonZero {
				if !foundNonZero {
					firstNonZero = nDigitsRead
				}
				foundNonZero = true
				digits[digitsInsertPosition] = uint16(str[strRead]) - '0'
				digitsInsertPosition++
				nDigitsStored++
			}
		}

		if foundNonZero {
			nDigits++
		}

		if sawRadix {
			radixPosition++
		}

		nDigitsRead++
		if strRead < strLen - 1 {
			strRead++
		} else {
			break
		}
	}

	if sawRadix && nDigitsRead == 0 {
		return MakeDec128NaN()
	}

	// Read exponent if it exists
	if str[strRead] == 'e' || str[strRead] == 'E' {
		// var nRead int = 0
		strRead++
		readExponent, err := strconv.Atoi(string(str[strRead:]))
		exponent = int32(readExponent)
		strRead = strLen - 1

		if err != nil {
			return MakeDec128NaN()
		}
	}

	if strRead != strLen - 1 {
		return MakeDec128NaN()
	}

	// Done reading input
	// Find first non-zero digit in digits
	if nDigitsStored == 0 {
		firstDigit = 0
		lastDigit = 0
		digits[0] = 0
		nDigits = 1
		nDigitsStored = 1
		nDigitsNoTrailing = 0
	} else {
		lastDigit = nDigitsStored - 1
		nDigitsNoTrailing = nDigits
		for str[firstNonZero + nDigitsNoTrailing - 1] == '0' {
			nDigitsNoTrailing--;
		}
	}

	// Normalization of exponent
	// Correct exponent based on radix position and shift significand as needed
	// to represent user input.

	// Overflow prevention
	if exponent <= int32(radixPosition) && int32(radixPosition) - exponent > (1 << 14) {
		exponent = int32(BSONDec128ExponentMin)
	} else {
		exponent -= int32(radixPosition)
	}

	// Attempt to normalize the exponent
	for exponent > int32(BSONDec128ExponentMax) {
		// Shift the exponent to significand and decrease
		lastDigit++

		if lastDigit - firstDigit > uint16(BSONDec128MaxDigits) {
			return MakeDec128Infinity(isNegative)
		}

		exponent--
	}

	for exponent < int32(BSONDec128ExponentMin) || nDigitsStored < nDigits {
		// Shift the last digit
		if lastDigit == 0 {
			exponent = int32(BSONDec128ExponentMin)
			// Signal zero value
			nDigitsNoTrailing = 0
			break;
		}

		if nDigitsStored < nDigits {
			// Adjust to match digits not stored
			nDigits--
		} else {
			// Adjust to round
			lastDigit--
		}

		if exponent < int32(BSONDec128ExponentMax) {
			exponent++
		} else {
			return MakeDec128Infinity(isNegative)
		}
	}

	// Round
	if lastDigit - firstDigit + 1 < nDigitsNoTrailing {
		// There are non-zero digits after lastDigit that need rounding
		// Use round to nearest, ties to even rounding mode
		var roundDigit uint8 = str[firstNonZero + lastDigit + 1] - '0'
		var roundBit bool = false

		if roundDigit >= 5 {
			roundBit = true

			if roundDigit == 5 {
				roundBit = (digits[lastDigit] % 2 == 1)

				for i := firstNonZero + lastDigit + 2; i < nDigitsRead; i++ {
					if (str[i] - '0') != 0 {
						roundBit = true
						break
					}
				}
			}
		}

		if roundBit {
			var dIdx uint16 = lastDigit
			for ; dIdx >= 0; dIdx-- {
				digits[dIdx]++
				if digits[dIdx] > 9 {
					digits[dIdx] = 0
					// Overflowed most significant digit
					if dIdx == 0 {
						if exponent < int32(BSONDec128ExponentMax) {
							exponent++
							digits[dIdx] = 1
							break
						} else {
							return MakeDec128Infinity(isNegative)
						}
					}
				} else {
					break
				}
			}
		}
	}

	// Encode significand
	var significandHigh uint64
	var significandLow uint64

	if nDigitsNoTrailing == 0 {
		// If we read a zero, significand is zero
		significandHigh = 0
		significandLow = 0
	} else if lastDigit - firstDigit < 17 {
		// If we can fit the significand entirely into the low 64 bits
		var dIdx uint16 = firstDigit
		significandLow = uint64(digits[dIdx])
		dIdx++

		for ; dIdx <= lastDigit; dIdx++ {
			significandLow *= 10
			significandLow += uint64(digits[dIdx])
			significandHigh = 0
		}
	} else {
		// We need to use both the low 64 and high 64 bits
		var dIdx uint16 = firstDigit
		significandHigh = uint64(digits[dIdx])
		dIdx++

		for ; dIdx <= lastDigit - 17; dIdx++ {
			significandHigh *= 10
			significandHigh += uint64(digits[dIdx])
		}

		significandLow = uint64(digits[dIdx])
		dIdx++
		for ; dIdx <= lastDigit; dIdx++ {
			significandLow *= 10
			significandLow += uint64(digits[dIdx])
		}
	}

	significand := Multiply64x64(significandHigh, 100000000000000000)
	significand.Low += significandLow
	if significand.Low < significandLow {
		significand.High += 1
	}

	// Encode combination and exponent with significand
	var biasedExponent uint16 = uint16(exponent + int32(BSONDec128ExponentBias))
	var decHigh64 uint64
	var decLow64 uint64

	if (significand.High >> 49) & 1 != 0 {
		decHigh64 |= (0x3 << 61)
		decHigh64 |= uint64((biasedExponent & 0x3fff)) << 47
		decHigh64 |= (significand.High & 0x7fffffffffff)
	} else {
		decHigh64 |= uint64((biasedExponent & 0x3fff)) << 49
		decHigh64 |= (significand.High & 0x1ffffffffffff)
	}

	decLow64 = significand.Low

	// Encode sign
	if isNegative {
		decHigh64 |= 0x8000000000000000
	}

	result := Dec128{decLow64, decHigh64}
	return result
}

const initialBufferSize = 64

func handleErr(err *error) {
	if r := recover(); r != nil {
		if _, ok := r.(runtime.Error); ok {
			panic(r)
		} else if _, ok := r.(externalPanic); ok {
			panic(r)
		} else if s, ok := r.(string); ok {
			*err = errors.New(s)
		} else if e, ok := r.(error); ok {
			*err = e
		} else {
			panic(r)
		}
	}
}

// Marshal serializes the in value, which may be a map or a struct value.
// In the case of struct values, only exported fields will be serialized.
// The lowercased field name is used as the key for each exported field,
// but this behavior may be changed using the respective field tag.
// The tag may also contain flags to tweak the marshalling behavior for
// the field. The tag formats accepted are:
//
//     "[<key>][,<flag1>[,<flag2>]]"
//
//     `(...) bson:"[<key>][,<flag1>[,<flag2>]]" (...)`
//
// The following flags are currently supported:
//
//     omitempty  Only include the field if it's not set to the zero
//                value for the type or to empty slices or maps.
//
//     minsize    Marshal an int64 value as an int32, if that's feasible
//                while preserving the numeric value.
//
//     inline     Inline the field, which must be a struct or a map,
//                causing all of its fields or keys to be processed as if
//                they were part of the outer struct. For maps, keys must
//                not conflict with the bson keys of other struct fields.
//
// Some examples:
//
//     type T struct {
//         A bool
//         B int    "myb"
//         C string "myc,omitempty"
//         D string `bson:",omitempty" json:"jsonkey"`
//         E int64  ",minsize"
//         F int64  "myf,omitempty,minsize"
//     }
//
func Marshal(in interface{}) (out []byte, err error) {
	defer handleErr(&err)
	e := &encoder{make([]byte, 0, initialBufferSize)}
	e.addDoc(reflect.ValueOf(in))
	return e.out, nil
}

// Unmarshal deserializes data from in into the out value.  The out value
// must be a map, a pointer to a struct, or a pointer to a bson.D value.
// The lowercased field name is used as the key for each exported field,
// but this behavior may be changed using the respective field tag.
// The tag may also contain flags to tweak the marshalling behavior for
// the field. The tag formats accepted are:
//
//     "[<key>][,<flag1>[,<flag2>]]"
//
//     `(...) bson:"[<key>][,<flag1>[,<flag2>]]" (...)`
//
// The following flags are currently supported during unmarshal (see the
// Marshal method for other flags):
//
//     inline     Inline the field, which must be a struct or a map.
//                Inlined structs are handled as if its fields were part
//                of the outer struct. An inlined map causes keys that do
//                not match any other struct field to be inserted in the
//                map rather than being discarded as usual.
//
// The target field or element types of out may not necessarily match
// the BSON values of the provided data.  The following conversions are
// made automatically:
//
// - Numeric types are converted if at least the integer part of the
//   value would be preserved correctly
// - Bools are converted to numeric types as 1 or 0
// - Numeric types are converted to bools as true if not 0 or false otherwise
// - Binary and string BSON data is converted to a string, array or byte slice
//
// If the value would not fit the type and cannot be converted, it's
// silently skipped.
//
// Pointer values are initialized when necessary.
func Unmarshal(in []byte, out interface{}) (err error) {
	if raw, ok := out.(*Raw); ok {
		raw.Kind = 3
		raw.Data = in
		return nil
	}
	defer handleErr(&err)
	v := reflect.ValueOf(out)
	switch v.Kind() {
	case reflect.Ptr:
		fallthrough
	case reflect.Map:
		d := newDecoder(in)
		d.readDocTo(v)
	case reflect.Struct:
		return errors.New("Unmarshal can't deal with struct values. Use a pointer.")
	default:
		return errors.New("Unmarshal needs a map or a pointer to a struct.")
	}
	return nil
}

// Unmarshal deserializes raw into the out value.  If the out value type
// is not compatible with raw, a *bson.TypeError is returned.
//
// See the Unmarshal function documentation for more details on the
// unmarshalling process.
func (raw Raw) Unmarshal(out interface{}) (err error) {
	defer handleErr(&err)
	v := reflect.ValueOf(out)
	switch v.Kind() {
	case reflect.Ptr:
		v = v.Elem()
		fallthrough
	case reflect.Map:
		d := newDecoder(raw.Data)
		good := d.readElemTo(v, raw.Kind)
		if !good {
			return &TypeError{v.Type(), raw.Kind}
		}
	case reflect.Struct:
		return errors.New("Raw Unmarshal can't deal with struct values. Use a pointer.")
	default:
		return errors.New("Raw Unmarshal needs a map or a valid pointer.")
	}
	return nil
}

type TypeError struct {
	Type reflect.Type
	Kind byte
}

func (e *TypeError) Error() string {
	return fmt.Sprintf("BSON kind 0x%02x isn't compatible with type %s", e.Kind, e.Type.String())
}

// --------------------------------------------------------------------------
// Maintain a mapping of keys to structure field indexes

type structInfo struct {
	FieldsMap  map[string]fieldInfo
	FieldsList []fieldInfo
	InlineMap  int
	Zero       reflect.Value
}

type fieldInfo struct {
	Key       string
	Num       int
	OmitEmpty bool
	MinSize   bool
	Inline    []int
}

var structMap = make(map[reflect.Type]*structInfo)
var structMapMutex sync.RWMutex

type externalPanic string

func (e externalPanic) String() string {
	return string(e)
}

func getStructInfo(st reflect.Type) (*structInfo, error) {
	structMapMutex.RLock()
	sinfo, found := structMap[st]
	structMapMutex.RUnlock()
	if found {
		return sinfo, nil
	}
	n := st.NumField()
	fieldsMap := make(map[string]fieldInfo)
	fieldsList := make([]fieldInfo, 0, n)
	inlineMap := -1
	for i := 0; i != n; i++ {
		field := st.Field(i)
		if field.PkgPath != "" {
			continue // Private field
		}

		info := fieldInfo{Num: i}

		tag := field.Tag.Get("bson")
		if tag == "" && strings.Index(string(field.Tag), ":") < 0 {
			tag = string(field.Tag)
		}
		if tag == "-" {
			continue
		}

		// XXX Drop this after a few releases.
		if s := strings.Index(tag, "/"); s >= 0 {
			recommend := tag[:s]
			for _, c := range tag[s+1:] {
				switch c {
				case 'c':
					recommend += ",omitempty"
				case 's':
					recommend += ",minsize"
				default:
					msg := fmt.Sprintf("Unsupported flag %q in tag %q of type %s", string([]byte{uint8(c)}), tag, st)
					panic(externalPanic(msg))
				}
			}
			msg := fmt.Sprintf("Replace tag %q in field %s of type %s by %q", tag, field.Name, st, recommend)
			panic(externalPanic(msg))
		}

		inline := false
		fields := strings.Split(tag, ",")
		if len(fields) > 1 {
			for _, flag := range fields[1:] {
				switch flag {
				case "omitempty":
					info.OmitEmpty = true
				case "minsize":
					info.MinSize = true
				case "inline":
					inline = true
				default:
					msg := fmt.Sprintf("Unsupported flag %q in tag %q of type %s", flag, tag, st)
					panic(externalPanic(msg))
				}
			}
			tag = fields[0]
		}

		if inline {
			switch field.Type.Kind() {
			case reflect.Map:
				if inlineMap >= 0 {
					return nil, errors.New("Multiple ,inline maps in struct " + st.String())
				}
				if field.Type.Key() != reflect.TypeOf("") {
					return nil, errors.New("Option ,inline needs a map with string keys in struct " + st.String())
				}
				inlineMap = info.Num
			case reflect.Struct:
				sinfo, err := getStructInfo(field.Type)
				if err != nil {
					return nil, err
				}
				for _, finfo := range sinfo.FieldsList {
					if _, found := fieldsMap[finfo.Key]; found {
						msg := "Duplicated key '" + finfo.Key + "' in struct " + st.String()
						return nil, errors.New(msg)
					}
					if finfo.Inline == nil {
						finfo.Inline = []int{i, finfo.Num}
					} else {
						finfo.Inline = append([]int{i}, finfo.Inline...)
					}
					fieldsMap[finfo.Key] = finfo
					fieldsList = append(fieldsList, finfo)
				}
			default:
				panic("Option ,inline needs a struct value or map field")
			}
			continue
		}

		if tag != "" {
			info.Key = tag
		} else {
			info.Key = strings.ToLower(field.Name)
		}

		if _, found = fieldsMap[info.Key]; found {
			msg := "Duplicated key '" + info.Key + "' in struct " + st.String()
			return nil, errors.New(msg)
		}

		fieldsList = append(fieldsList, info)
		fieldsMap[info.Key] = info
	}
	sinfo = &structInfo{
		fieldsMap,
		fieldsList,
		inlineMap,
		reflect.New(st).Elem(),
	}
	structMapMutex.Lock()
	structMap[st] = sinfo
	structMapMutex.Unlock()
	return sinfo, nil
}
