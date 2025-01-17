// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package io provides basic interfaces to I/O primitives.
// Its primary job is to wrap existing implementations of such primitives,
// such as those in package os, into shared public interfaces that
// abstract the functionality, plus some other related primitives.
// 包io提供了I/O原语的基本接口。
// 它的主要工作是将此类原语的现有实现（例如 os 包中的那些实现）包装到
// 抽象功能的共享公共接口以及一些其他相关原语中。
//
// Because these interfaces and primitives wrap lower-level operations with
// various implementations, unless otherwise informed clients should not
// assume they are safe for parallel execution.
// 因为这些接口和原语用各种实现包装了较低级别的操作，除非另有通知，否则客户端不应假定它们可以安全地并行执行。
package io

import (
	"errors"
	"sync"
)

// Seek whence values.
const (
	SeekStart   = 0 // seek relative to the origin of the file
	SeekCurrent = 1 // seek relative to the current offset
	SeekEnd     = 2 // seek relative to the end
)

// ErrShortWrite means that a write accepted fewer bytes than requested
// but failed to return an explicit error.
var ErrShortWrite = errors.New("short write")

// errInvalidWrite means that a write returned an impossible count.
var errInvalidWrite = errors.New("invalid write result")

// ErrShortBuffer means that a read required a longer buffer than was provided.
var ErrShortBuffer = errors.New("short buffer")

// EOF is the error returned by Read when no more input is available.
// (Read must return EOF itself, not an error wrapping EOF,
// because callers will test for EOF using ==.)
// Functions should return EOF only to signal a graceful end of input.
// If the EOF occurs unexpectedly in a structured data stream,
// the appropriate error is either ErrUnexpectedEOF or some other error
// giving more detail.
var EOF = errors.New("EOF")

// ErrUnexpectedEOF means that EOF was encountered in the
// middle of reading a fixed-size block or data structure.
var ErrUnexpectedEOF = errors.New("unexpected EOF")

// ErrNoProgress is returned by some clients of a Reader when
// many calls to Read have failed to return any data or error,
// usually the sign of a broken Reader implementation.
var ErrNoProgress = errors.New("multiple Read calls return no data or error")

// Reader is the interface that wraps the basic Read method.
// Reader 是包装了基本Read方法的接口。
//
// Read reads up to len(p) bytes into p. It returns the number of bytes
// read (0 <= n <= len(p)) and any error encountered. Even if Read
// returns n < len(p), it may use all of p as scratch space during the call.
// If some data is available but not len(p) bytes, Read conventionally
// returns what is available instead of waiting for more.
// Read 读取多达len(p)个自己到 p 。它返回读取的字节数(0 <= n <= len(p)) 以及任何遇到的错误。
// 即使 Read 返回 n < len(p)，但在调用期间它可以使用整个 p 作为暂存空间。
// 假如有一些数据是可用的但是长度没有len(p)个字节，Read 通常返回可用的数据而不是等待更多数据。
//
// When Read encounters an error or end-of-file condition after
// successfully reading n > 0 bytes, it returns the number of
// bytes read. It may return the (non-nil) error from the same call
// or return the error (and n == 0) from a subsequent call.
// An instance of this general case is that a Reader returning
// a non-zero number of bytes at the end of the input stream may
// return either err == EOF or err == nil. The next Read should
// return 0, EOF.
// 当 Read 在成功读取 n > 0 个字节后遇到了错误或到达了文件的结尾，它返回读取的字节数。
// 它可以在当前调用中返回非nil错误，或者在下一次调用时返回错误且n为0。
// 这种一般情况下的一个例子是，如果Reader在输入流末尾返回非0字节数，它可能返回err == EOF
// 或 err == nil。下一次 Read 时应该返回 0，EOF。
//
// Callers should always process the n > 0 bytes returned before
// considering the error err. Doing so correctly handles I/O errors
// that happen after reading some bytes and also both of the
// allowed EOF behaviors.
// 在考虑错误err之前，调用方应始终处理返回的 n > 0 个字节。 这样做可以正确处理
// 读取某些字节后发生的I/O错误以及两种允许的EOF行为（译注：即上面提到的两种方式）。
//
// Implementations of Read are discouraged from returning a
// zero byte count with a nil error, except when len(p) == 0.
// Callers should treat a return of 0 and nil as indicating that
// nothing happened; in particular it does not indicate EOF.
// 不鼓励Read的实现返回一个0字节的计数和一个nil错误，除非len(p) == 0。
// 调用者应该将返回的0和nil看作什么也没有发生；特别的是它不表示EOF。
//
// Implementations must not retain p.
// 实现不得保留 p 。（译注：即不能把p缓存下来）
type Reader interface {
	Read(p []byte) (n int, err error)
}

// Writer is the interface that wraps the basic Write method.
// Writer 是封装了基本Write方法的接口。
//
// Write writes len(p) bytes from p to the underlying data stream.
// It returns the number of bytes written from p (0 <= n <= len(p))
// and any error encountered that caused the write to stop early.
// Write must return a non-nil error if it returns n < len(p).
// Write must not modify the slice data, even temporarily.
// Write 写把p的len(p)个字节写入到底层的数据流中。
// 它返回写入的字节数（0 <= n <= len(p))，以及遇到的造成写入提前终止任何错误。
// 如果 Write 返回的字节数n<len(p)，它必须返回一个非nil错误。
// Write 不能修改切片 p 的数据，哪怕是暂时的。
//
// Implementations must not retain p.
// 实现方不能保留 p 。
type Writer interface {
	Write(p []byte) (n int, err error)
}

// Closer is the interface that wraps the basic Close method.
// Closer 是封装了基础Close方法的接口。
//
// The behavior of Close after the first call is undefined.
// Specific implementations may document their own behavior.
// 在第一次调用Close方法后再次调用它的行为是未定义的。
// 具体的实现者可以记录它们自己的行为。
type Closer interface {
	Close() error
}

// Seeker is the interface that wraps the basic Seek method.
// Seeker 是封装了基本Seek方法的接口。
//
// Seek sets the offset for the next Read or Write to offset,
// interpreted according to whence:
// SeekStart means relative to the start of the file,
// SeekCurrent means relative to the current offset, and
// SeekEnd means relative to the end
// (for example, offset = -2 specifies the penultimate byte of the file).
// Seek returns the new offset relative to the start of the
// file or an error, if any.
// Seek 将下一次Read或Write的偏移量设置为offset，依据whence解释：
// SeekStart 意思是相对于文件的开始；
// SeekCurrent 意思是相对于当前偏移量；
// SeekEnd 意思是相对于文件的末尾；
// （例如，偏移量offset = -2 特指文件的倒数第二个字节）。
// Seek 返回相对于起始文件的新的偏移量offset或者一个错误，如果有错误的话。
//
// Seeking to an offset before the start of the file is an error.
// Seeking to any positive offset may be allowed, but if the new offset exceeds
// the size of the underlying object the behavior of subsequent I/O operations
// is implementation-dependent.
// 在文件开始之前寻找偏移量是错误的。
// 允许寻找任何正的偏移量，但是如果新的偏移量超过了底层对象的大小，则后续I/O操作的行为取决于实现方。
type Seeker interface {
	Seek(offset int64, whence int) (int64, error)
}

// ReadWriter is the interface that groups the basic Read and Write methods.
type ReadWriter interface {
	Reader
	Writer
}

// ReadCloser is the interface that groups the basic Read and Close methods.
type ReadCloser interface {
	Reader
	Closer
}

// WriteCloser is the interface that groups the basic Write and Close methods.
type WriteCloser interface {
	Writer
	Closer
}

// ReadWriteCloser is the interface that groups the basic Read, Write and Close methods.
type ReadWriteCloser interface {
	Reader
	Writer
	Closer
}

// ReadSeeker is the interface that groups the basic Read and Seek methods.
type ReadSeeker interface {
	Reader
	Seeker
}

// ReadSeekCloser is the interface that groups the basic Read, Seek and Close
// methods.
type ReadSeekCloser interface {
	Reader
	Seeker
	Closer
}

// WriteSeeker is the interface that groups the basic Write and Seek methods.
type WriteSeeker interface {
	Writer
	Seeker
}

// ReadWriteSeeker is the interface that groups the basic Read, Write and Seek methods.
type ReadWriteSeeker interface {
	Reader
	Writer
	Seeker
}

// ReaderFrom is the interface that wraps the ReadFrom method.
// ReaderFrom 是包装了ReadFrom方法的接口。
//
// ReadFrom reads data from r until EOF or error.
// The return value n is the number of bytes read.
// Any error except EOF encountered during the read is also returned.
// ReadFrom 从r读取数据直到出现EOF或错误。
// 返回值 n 是读取的字节个数。
// 读取过程中遇到的除 EOF 之外的任何错误也将返回（译注：即EOF错误不会被返回）。
//
// The Copy function uses ReaderFrom if available.
// Copy 函数使用 ReaderFrom（如果可用）。
type ReaderFrom interface {
	ReadFrom(r Reader) (n int64, err error)
}

// WriterTo is the interface that wraps the WriteTo method.
// WriterTo 是封装WriteTo方法的接口。
//
// WriteTo writes data to w until there's no more data to write or
// when an error occurs. The return value n is the number of bytes
// written. Any error encountered during the write is also returned.
// WriteTo 写入数据到 w 直到没有更多的数据可写或者当有错误发生时。返回值 n 是
// 已写入的字节大小。在写的过程中遇到的任何错误也会被返回。
//
// The Copy function uses WriterTo if available.
// Copy 函数使用 WriterTo（如果可用）。
type WriterTo interface {
	WriteTo(w Writer) (n int64, err error)
}

// ReaderAt is the interface that wraps the basic ReadAt method.
// ReaderAt 是包装基本ReadAt方法的接口。
//
// ReadAt reads len(p) bytes into p starting at offset off in the
// underlying input source. It returns the number of bytes
// read (0 <= n <= len(p)) and any error encountered.
// ReadAt 从底层输入源的偏移off的位置开始读取len(p)个字节到 p 中。
// 它返回读取的字节数 n (0 <= n <= len(p)) 和任何遇到的错误。
//
// When ReadAt returns n < len(p), it returns a non-nil error
// explaining why more bytes were not returned. In this respect,
// ReadAt is stricter than Read.
// 当 ReadAt 返回 n < len(p)，它返回一个非nil错误来解释为什么没有更多的字节返回回来。
// 在这方面，ReadAt比Read更加严格。
//
// Even if ReadAt returns n < len(p), it may use all of p as scratch
// space during the call. If some data is available but not len(p) bytes,
// ReadAt blocks until either all the data is available or an error occurs.
// In this respect ReadAt is different from Read.
// 即使 ReadAt 返回 n < len(p)，在调用过程中它也可以使用 p 的所有空间作为暂存空间。
// 如果一些数据是可用的但是没有len(p)个字节数，ReadAt将会一直阻塞直到所需要的数据都
// 准备好了或者遇到一个错误（译注：这点比Read函数严格，Read函数可以直接返回）。
// 从这方面来说ReadAt和Read不同。
//
// If the n = len(p) bytes returned by ReadAt are at the end of the
// input source, ReadAt may return either err == EOF or err == nil.
// 如果 ReadAt 返回 n = len(p) 个字节时已经到达了输入源的末尾，那么它既可以返回
// err == EOF 也可以返回 err == nil。
//
// If ReadAt is reading from an input source with a seek offset,
// ReadAt should not affect nor be affected by the underlying
// seek offset.
// 如果 ReadAt 正在从具有位置偏移量的底层读取数据，那么ReadAt既不应该影响底层的位置
// 偏移量，反之也不应该受到它的影响。
//
// Clients of ReadAt can execute parallel ReadAt calls on the
// same input source.
// ReadAt的客户端能在同样的输入源上并行的执行ReadAt调用。
//
// Implementations must not retain p.
// 实现者不能保留 p 。
type ReaderAt interface {
	ReadAt(p []byte, off int64) (n int, err error)
}

// WriterAt is the interface that wraps the basic WriteAt method.
// WriterAt 是包装基本WriteAt方法的接口。
//
// WriteAt writes len(p) bytes from p to the underlying data stream
// at offset off. It returns the number of bytes written from p (0 <= n <= len(p))
// and any error encountered that caused the write to stop early.
// WriteAt must return a non-nil error if it returns n < len(p).
// WriteAt 向底层数据源的off偏移量开始写入 len(p) 个字节。
// 它返回从 p（0 <= n <= len(p)）写入的字节数以及造成写入提前终止的任何错误。
// 如果写入的字节数 n < len(p) 那么 WriteAt 必须返回一个非nil错误。
//
// If WriteAt is writing to a destination with a seek offset,
// WriteAt should not affect nor be affected by the underlying
// seek offset.
// 如果 WriteAt 正在向一个带了位置偏移量的目标写入时，WriteAt既不应该影响
// 底层偏移量，反之也不应该受它的影响。
//
// Clients of WriteAt can execute parallel WriteAt calls on the same
// destination if the ranges do not overlap.
// 如果范围不重叠，WriteAt 的客户端可以在同一目标上执行并行 WriteAt 调用。
//
// Implementations must not retain p.
// 实现者不能保留 p 。
type WriterAt interface {
	WriteAt(p []byte, off int64) (n int, err error)
}

// ByteReader is the interface that wraps the ReadByte method.
// ByteReader 是包装了基本ReadByte方法的接口。
//
// ReadByte reads and returns the next byte from the input or
// any error encountered. If ReadByte returns an error, no input
// byte was consumed, and the returned byte value is undefined.
// ReadByte 从输入源读取和返回下一个字节或者错误。如果返回错误，则没有输入字节
// 被消费，并且返回的字节值是未定义的。
//
// ReadByte provides an efficient interface for byte-at-time
// processing. A Reader that does not implement  ByteReader
// can be wrapped using bufio.NewReader to add this method.
// ReadByte 为逐字节处理提供了一个有效的接口。
// 可以使用 bufio.NewReader 包装未实现 ByteReader 的 Reader 以添加此方法。
type ByteReader interface {
	ReadByte() (byte, error)
}

// ByteScanner is the interface that adds the UnreadByte method to the
// basic ReadByte method.
// ByteScanner 是将 UnreadByte 方法添加到基本 ReadByte 方法的接口。
//
// UnreadByte causes the next call to ReadByte to return the last byte read.
// If the last operation was not a successful call to ReadByte, UnreadByte may
// return an error, unread the last byte read (or the byte prior to the
// last-unread byte), or (in implementations that support the Seeker interface)
// seek to one byte before the current offset.
// UnreadByte 导致对 ReadByte 的下一次调用返回读取的最后一个字节。 如果最后的操作
// 不是对 ReadByte 的成功调用，UnreadByte 可能会返回一个错误，未读取的最后一个字节
// （或最后一个未读字节之前的字节），或者（在支持 Seeker 接口的实现中）寻找一个字节 在当前偏移量之前。
// （译注：不是太理解这段话）
type ByteScanner interface {
	ByteReader
	UnreadByte() error
}

// ByteWriter is the interface that wraps the WriteByte method.
// ByteWriter 是包装了 WriteByte 方法的接口。
type ByteWriter interface {
	WriteByte(c byte) error
}

// RuneReader is the interface that wraps the ReadRune method.
// RuneReader 是包装了 ReadRune 方法的接口。
//
// ReadRune reads a single encoded Unicode character
// and returns the rune and its size in bytes. If no character is
// available, err will be set.
// ReadRune 读取单个编码的 Unicode 字符并返回符文及其大小（以字节为单位）。
// 如果没有字符可用，将设置 err。
type RuneReader interface {
	ReadRune() (r rune, size int, err error)
}

// RuneScanner is the interface that adds the UnreadRune method to the
// basic ReadRune method.
//
// UnreadRune causes the next call to ReadRune to return the last rune read.
// If the last operation was not a successful call to ReadRune, UnreadRune may
// return an error, unread the last rune read (or the rune prior to the
// last-unread rune), or (in implementations that support the Seeker interface)
// seek to the start of the rune before the current offset.
type RuneScanner interface {
	RuneReader
	UnreadRune() error
}

// StringWriter is the interface that wraps the WriteString method.
type StringWriter interface {
	WriteString(s string) (n int, err error)
}

// WriteString writes the contents of the string s to w, which accepts a slice of bytes.
// If w implements StringWriter, its WriteString method is invoked directly.
// Otherwise, w.Write is called exactly once.
// WriteString 把字符串 s 的内容写入到 w 中，w接受一个字节切片。
// 如果 w 实施了 StringWriter 方法，则直接调用这个方法。
// 否则，w.Write 方法将会被调用。
func WriteString(w Writer, s string) (n int, err error) {
	if sw, ok := w.(StringWriter); ok {
		return sw.WriteString(s)
	}
	return w.Write([]byte(s))
}

// ReadAtLeast reads from r into buf until it has read at least min bytes.
// It returns the number of bytes copied and an error if fewer bytes were read.
// The error is EOF only if no bytes were read.
// If an EOF happens after reading fewer than min bytes,
// ReadAtLeast returns ErrUnexpectedEOF.
// If min is greater than the length of buf, ReadAtLeast returns ErrShortBuffer.
// On return, n >= min if and only if err == nil.
// If r returns an error having read at least min bytes, the error is dropped.
// ReadAtLeast 从 r 至少读取 min 个字节到 buf 中。
// 它返回复制的字节数和一个错误如果读取的字节数少于 min 的话。
// 只有在没有字节可读的情况下才返回EOF错误。
// 如果在读取少于 min 个字节后遇到了 EOF ，ReadAtLeast将返回 ErrUnexpectedEOF。
// 如果 min 大于 buf 的长度，ReadAtLeast 返回 ErrShortBuffer 。
// 返回nil错误的条件是当且仅当 n >= min。（译注：根据代码意译）
// 如果 r 返回错误时已经读取了至少 min 个字节，则错误将被丢弃。
func ReadAtLeast(r Reader, buf []byte, min int) (n int, err error) {
	if len(buf) < min {
		return 0, ErrShortBuffer
	}
	for n < min && err == nil {
		var nn int
		nn, err = r.Read(buf[n:])
		n += nn
	}
	if n >= min {
		err = nil
	} else if n > 0 && err == EOF {
		err = ErrUnexpectedEOF
	}
	return
}

// ReadFull reads exactly len(buf) bytes from r into buf.
// ReadFull 从 r 中准确读取 len(buf) 个字节到 buf 中。
// It returns the number of bytes copied and an error if fewer bytes were read.
// The error is EOF only if no bytes were read.
// If an EOF happens after reading some but not all the bytes,
// ReadFull returns ErrUnexpectedEOF.
// On return, n == len(buf) if and only if err == nil.
// 返回时，n == len(buf)  当且仅当 err == nil。
// If r returns an error having read at least len(buf) bytes, the error is dropped.
// 如果已经至少读取了 len(buf) 个字节，但是返回了错误，那么这个错误将会被丢弃。
func ReadFull(r Reader, buf []byte) (n int, err error) {
	return ReadAtLeast(r, buf, len(buf))
}

// CopyN copies n bytes (or until an error) from src to dst.
// It returns the number of bytes copied and the earliest
// error encountered while copying.
// On return, written == n if and only if err == nil.
//
// If dst implements the ReaderFrom interface,
// the copy is implemented using it.
func CopyN(dst Writer, src Reader, n int64) (written int64, err error) {
	written, err = Copy(dst, LimitReader(src, n))
	if written == n {
		return n, nil
	}
	if written < n && err == nil {
		// src stopped early; must have been EOF.
		err = EOF
	}
	return
}

// Copy copies from src to dst until either EOF is reached
// on src or an error occurs. It returns the number of bytes
// copied and the first error encountered while copying, if any.
// Copy 复制 src 到 dst 直到在src上遇到EOF 或者 产生一个错误。
// 它返回复制的字节数以及在复制中遇到的第一个错误，假如有的话。
//
// A successful Copy returns err == nil, not err == EOF.
// Because Copy is defined to read from src until EOF, it does
// not treat an EOF from Read as an error to be reported.
// 一个成功的Copy返回 err == nil，而不是 err == EOF。
// 因为 Copy 被定义为从 src 读取直到 EOF，它不会将 Read 中的 EOF 视为要报告的错误。
//
// If src implements the WriterTo interface,
// the copy is implemented by calling src.WriteTo(dst).
// Otherwise, if dst implements the ReaderFrom interface,
// the copy is implemented by calling dst.ReadFrom(src).
// 如果 src 实现了 WriterTo 接口，
// 复制是通过调用 src.WriteTo(dst) 实现的。
// 否则，如果 dst 实现了 ReaderFrom 接口，
// 拷贝是通过调用dst.ReadFrom(src)实现的。
func Copy(dst Writer, src Reader) (written int64, err error) {
	return copyBuffer(dst, src, nil)
}

// CopyBuffer is identical to Copy except that it stages through the
// provided buffer (if one is required) rather than allocating a
// temporary one. If buf is nil, one is allocated; otherwise if it has
// zero length, CopyBuffer panics.
// CopyBuffer 与 Copy 相同，只是它通过提供缓冲区（如果需要的话）而不是分配一个
// 临时的。 如果 buf 为 nil，则分配一个； 否则如果它的长度为零，CopyBuffer
// 抛出异常（panics）。
//
// If either src implements WriterTo or dst implements ReaderFrom,
// buf will not be used to perform the copy.
// 如果 src 实现了 WriterTo 或者 dst 实现了 ReaderFrom，
// buf 不会用于执行复制。
func CopyBuffer(dst Writer, src Reader, buf []byte) (written int64, err error) {
	if buf != nil && len(buf) == 0 {
		panic("empty buffer in CopyBuffer")
	}
	return copyBuffer(dst, src, buf)
}

// copyBuffer is the actual implementation of Copy and CopyBuffer.
// if buf is nil, one is allocated.
// copyBuffer 是 Copy 和 CopyBuffer 的实际实现。
// 如果 buf 为 nil，则分配一个。
func copyBuffer(dst Writer, src Reader, buf []byte) (written int64, err error) {
	// If the reader has a WriteTo method, use it to do the copy.
	// Avoids an allocation and a copy.
	if wt, ok := src.(WriterTo); ok {
		return wt.WriteTo(dst)
	}
	// Similarly, if the writer has a ReadFrom method, use it to do the copy.
	if rt, ok := dst.(ReaderFrom); ok {
		return rt.ReadFrom(src)
	}
	if buf == nil {
		size := 32 * 1024
		// 为 LimitedReader 做了特殊处理
		if l, ok := src.(*LimitedReader); ok && int64(size) > l.N {
			if l.N < 1 {
				size = 1
			} else {
				size = int(l.N)
			}
		}
		buf = make([]byte, size)
	}
	for {
		// 把 src 的内容循环读取到 buf，然后再将 buf 的内容写入到 dst 中
		nr, er := src.Read(buf)
		if nr > 0 {
			nw, ew := dst.Write(buf[0:nr])
			if nw < 0 || nr < nw {
				nw = 0
				if ew == nil {
					ew = errInvalidWrite
				}
			}
			written += int64(nw)
			if ew != nil {
				err = ew
				break
			}
			if nr != nw {
				err = ErrShortWrite
				break
			}
		}
		if er != nil {
			if er != EOF {
				err = er
			}
			break
		}
	}
	return written, err
}

// LimitReader returns a Reader that reads from r
// but stops with EOF after n bytes.
// The underlying implementation is a *LimitedReader.
// LimitReader 返回一个从 r 读取的 Reader
// 但在 n 个字节后以 EOF 停止。
// 底层实现是一个 *LimitedReader。
func LimitReader(r Reader, n int64) Reader { return &LimitedReader{r, n} }

// A LimitedReader reads from R but limits the amount of
// data returned to just N bytes. Each call to Read
// updates N to reflect the new amount remaining.
// Read returns EOF when N <= 0 or when the underlying R returns EOF.
// LimitedReader 从 R 中读取数据但限制了数量
// 返回的数据只有 N 个字节。 每次调用 Read
// 更新 N 以反映新的剩余数量。
// 当 N <= 0 或底层 R 返回 EOF 时，Read 返回 EOF。
type LimitedReader struct {
	R Reader // underlying reader
	N int64  // max bytes remaining
}

func (l *LimitedReader) Read(p []byte) (n int, err error) {
	if l.N <= 0 {
		return 0, EOF
	}
	if int64(len(p)) > l.N {
		p = p[0:l.N]
	}
	n, err = l.R.Read(p)
	l.N -= int64(n)
	return
}

// NewSectionReader returns a SectionReader that reads from r
// starting at offset off and stops with EOF after n bytes.
// NewSectionReader 返回一个从 r 读取的 SectionReader
// 从偏移量 off 开始，在 n 个字节后以 EOF 停止。
func NewSectionReader(r ReaderAt, off int64, n int64) *SectionReader {
	var remaining int64
	const maxint64 = 1<<63 - 1
	if off <= maxint64-n {
		remaining = n + off
	} else {
		// Overflow, with no way to return error.
		// Assume we can read up to an offset of 1<<63 - 1.
		remaining = maxint64
	}
	return &SectionReader{r, off, off, remaining}
}

// SectionReader implements Read, Seek, and ReadAt on a section
// of an underlying ReaderAt.
// SectionReader 在底层ReaderAt的区间上实现 Read、Seek 和 ReadAt。
type SectionReader struct {
	r     ReaderAt
	base  int64
	off   int64
	limit int64
}

func (s *SectionReader) Read(p []byte) (n int, err error) {
	if s.off >= s.limit {
		return 0, EOF
	}
	if max := s.limit - s.off; int64(len(p)) > max {
		p = p[0:max]
	}
	n, err = s.r.ReadAt(p, s.off)
	s.off += int64(n)
	return
}

var errWhence = errors.New("Seek: invalid whence")
var errOffset = errors.New("Seek: invalid offset")

func (s *SectionReader) Seek(offset int64, whence int) (int64, error) {
	switch whence {
	default:
		return 0, errWhence
	case SeekStart:
		offset += s.base
	case SeekCurrent:
		offset += s.off
	case SeekEnd:
		offset += s.limit
	}
	if offset < s.base {
		return 0, errOffset
	}
	s.off = offset
	return offset - s.base, nil
}

func (s *SectionReader) ReadAt(p []byte, off int64) (n int, err error) {
	if off < 0 || off >= s.limit-s.base {
		return 0, EOF
	}
	off += s.base
	if max := s.limit - off; int64(len(p)) > max {
		p = p[0:max]
		n, err = s.r.ReadAt(p, off)
		if err == nil {
			err = EOF
		}
		return n, err
	}
	return s.r.ReadAt(p, off)
}

// Size returns the size of the section in bytes.
func (s *SectionReader) Size() int64 { return s.limit - s.base }

// TeeReader returns a Reader that writes to w what it reads from r.
// All reads from r performed through it are matched with
// corresponding writes to w. There is no internal buffering -
// the write must complete before the read completes.
// Any error encountered while writing is reported as a read error.
// TeeReader 返回一个 Reader，它将从 r 读取的内容写入 w。
// 通过它执行的所有从 r 的读取都匹配
// 对应的写入w。 没有内部缓冲 -
// 写入必须在读取完成之前完成。
// 写入时遇到的任何错误都报告为读取错误。
func TeeReader(r Reader, w Writer) Reader {
	return &teeReader{r, w}
}

type teeReader struct {
	r Reader
	w Writer
}

func (t *teeReader) Read(p []byte) (n int, err error) {
	n, err = t.r.Read(p)
	if n > 0 {
		if n, err := t.w.Write(p[:n]); err != nil {
			return n, err
		}
	}
	return
}

// Discard is a Writer on which all Write calls succeed
// without doing anything.
var Discard Writer = discard{}

type discard struct{}

// discard implements ReaderFrom as an optimization so Copy to
// io.Discard can avoid doing unnecessary work.
var _ ReaderFrom = discard{}

func (discard) Write(p []byte) (int, error) {
	return len(p), nil
}

func (discard) WriteString(s string) (int, error) {
	return len(s), nil
}

var blackHolePool = sync.Pool{
	New: func() any {
		b := make([]byte, 8192)
		return &b
	},
}

func (discard) ReadFrom(r Reader) (n int64, err error) {
	bufp := blackHolePool.Get().(*[]byte)
	readSize := 0
	for {
		readSize, err = r.Read(*bufp)
		n += int64(readSize)
		if err != nil {
			blackHolePool.Put(bufp)
			if err == EOF {
				return n, nil
			}
			return
		}
	}
}

// NopCloser returns a ReadCloser with a no-op Close method wrapping
// the provided Reader r.
// If r implements WriterTo, the returned ReadCloser will implement WriterTo
// by forwarding calls to r.
func NopCloser(r Reader) ReadCloser {
	if _, ok := r.(WriterTo); ok {
		return nopCloserWriterTo{r}
	}
	return nopCloser{r}
}

type nopCloser struct {
	Reader
}

func (nopCloser) Close() error { return nil }

type nopCloserWriterTo struct {
	Reader
}

func (nopCloserWriterTo) Close() error { return nil }

func (c nopCloserWriterTo) WriteTo(w Writer) (n int64, err error) {
	return c.Reader.(WriterTo).WriteTo(w)
}

// ReadAll reads from r until an error or EOF and returns the data it read.
// A successful call returns err == nil, not err == EOF. Because ReadAll is
// defined to read from src until EOF, it does not treat an EOF from Read
// as an error to be reported.
// ReadAll 从 r 读取数据直到出现错误或 EOF 并返回它读取的数据。
// 调用成功返回 err == nil，而不是 err == EOF。 因为 ReadAll 是
// 定义为从 src 读取直到 EOF，所以它不会把来自 Read 的 EOF
// 作为要报告的错误。
func ReadAll(r Reader) ([]byte, error) {
	b := make([]byte, 0, 512)
	for {
		if len(b) == cap(b) {
			// Add more capacity (let append pick how much).
			b = append(b, 0)[:len(b)]
		}
		n, err := r.Read(b[len(b):cap(b)])
		b = b[:len(b)+n]
		if err != nil {
			if err == EOF {
				err = nil
			}
			return b, err
		}
	}
}
