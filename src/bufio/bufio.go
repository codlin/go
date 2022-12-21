// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package bufio implements buffered I/O. It wraps an io.Reader or io.Writer
// object, creating another object (Reader or Writer) that also implements
// the interface but provides buffering and some help for textual I/O.
// 包 bufio 实施了缓存的I/O。它通过包装 io.Reader 或 io.Writer对象创建了另一个对象
// （Reader或Writer），新对象同样实施了被包装对象的接口，但是为文本化的I/O提供了缓存
// 和一些有用的帮助。
package bufio

import (
	"bytes"
	"errors"
	"io"
	"strings"
	"unicode/utf8"
)

const (
	defaultBufSize = 4096
)

var (
	ErrInvalidUnreadByte = errors.New("bufio: invalid use of UnreadByte")
	ErrInvalidUnreadRune = errors.New("bufio: invalid use of UnreadRune")
	ErrBufferFull        = errors.New("bufio: buffer full")
	ErrNegativeCount     = errors.New("bufio: negative count")
)

// Buffered input.

// Reader implements buffering for an io.Reader object.
type Reader struct {
	buf          []byte
	rd           io.Reader // reader provided by the client
	r, w         int       // buf read and write positions
	err          error
	lastByte     int // last byte read for UnreadByte; -1 means invalid
	lastRuneSize int // size of last rune read for UnreadRune; -1 means invalid
}

const minReadBufferSize = 16
const maxConsecutiveEmptyReads = 100

// NewReaderSize returns a new Reader whose buffer has at least the specified
// size. If the argument io.Reader is already a Reader with large enough
// size, it returns the underlying Reader.
// NewReaderSize 返回一个长度至少是指定缓存大小的新Reader。
// 如果参数io.Reader已经是Reader类型且缓存长度已经满足了要求，则直接返回这个io.Reader。
func NewReaderSize(rd io.Reader, size int) *Reader {
	// Is it already a Reader?
	b, ok := rd.(*Reader)
	if ok && len(b.buf) >= size {
		return b
	}
	if size < minReadBufferSize {
		size = minReadBufferSize
	}
	r := new(Reader)
	r.reset(make([]byte, size), rd)
	return r
}

// NewReader returns a new Reader whose buffer has the default size.
func NewReader(rd io.Reader) *Reader {
	return NewReaderSize(rd, defaultBufSize)
}

// Size returns the size of the underlying buffer in bytes.
func (b *Reader) Size() int { return len(b.buf) }

// Reset discards any buffered data, resets all state, and switches
// the buffered reader to read from r.
// Calling Reset on the zero value of Reader initializes the internal buffer
// to the default size.
func (b *Reader) Reset(r io.Reader) {
	if b.buf == nil {
		b.buf = make([]byte, defaultBufSize)
	}
	b.reset(b.buf, r)
}

func (b *Reader) reset(buf []byte, r io.Reader) {
	*b = Reader{
		buf:          buf,
		rd:           r,
		lastByte:     -1,
		lastRuneSize: -1,
	}
}

var errNegativeRead = errors.New("bufio: reader returned negative count from Read")

// fill reads a new chunk into the buffer.
func (b *Reader) fill() {
	// Slide existing data to beginning.
	if b.r > 0 {
		copy(b.buf, b.buf[b.r:b.w])
		b.w -= b.r
		b.r = 0
	}

	if b.w >= len(b.buf) {
		panic("bufio: tried to fill full buffer")
	}

	// Read new data: try a limited number of times.
	// 如果读取为空，连续读空的最大次数为maxConsecutiveEmptyReads
	for i := maxConsecutiveEmptyReads; i > 0; i-- {
		n, err := b.rd.Read(b.buf[b.w:])
		if n < 0 {
			panic(errNegativeRead)
		}
		b.w += n
		if err != nil {
			b.err = err
			return
		}
		if n > 0 {
			return
		}
	}
	b.err = io.ErrNoProgress
}

func (b *Reader) readErr() error {
	err := b.err
	b.err = nil
	return err
}

// Peek returns the next n bytes without advancing the reader. The bytes stop
// being valid at the next read call. If Peek returns fewer than n bytes, it
// also returns an error explaining why the read is short. The error is
// ErrBufferFull if n is larger than b's buffer size.
// Peek 返回下n个字节而不推进reader。字节在下一次读取调用时不再有效。
// 如果 Peek 返回的字节数少于n，它需要返回一个错误来解释为什么读取少了。
// 错误是 ErrBufferFull 的意思是n大于b的缓存长度。
//
// Calling Peek prevents a UnreadByte or UnreadRune call from succeeding
// until the next read operation.
// 调用Peek将会阻止UnreadByte或UnreadRune的调用直到下一次读取操作成功之前。
func (b *Reader) Peek(n int) ([]byte, error) {
	if n < 0 {
		return nil, ErrNegativeCount
	}

	b.lastByte = -1
	b.lastRuneSize = -1

	for b.w-b.r < n && b.w-b.r < len(b.buf) && b.err == nil {
		b.fill() // b.w-b.r < len(b.buf) => buffer is not full
	}

	if n > len(b.buf) {
		return b.buf[b.r:b.w], ErrBufferFull
	}

	// 0 <= n <= len(b.buf)
	var err error
	if avail := b.w - b.r; avail < n {
		// not enough data in buffer
		n = avail
		err = b.readErr()
		if err == nil {
			err = ErrBufferFull
		}
	}
	return b.buf[b.r : b.r+n], err
}

// Discard skips the next n bytes, returning the number of bytes discarded.
// Discard 跳过下n个字节，返回被丢弃的字节数。
//
// If Discard skips fewer than n bytes, it also returns an error.
// If 0 <= n <= b.Buffered(), Discard is guaranteed to succeed without
// reading from the underlying io.Reader.
// 如果 Discard 跳过的字节数少于n，它也会返回一个错误。
// 如果 0 <= n <= b.Buffered()，Discard确保成功而无需从底层io.Reader读取。
func (b *Reader) Discard(n int) (discarded int, err error) {
	if n < 0 {
		return 0, ErrNegativeCount
	}
	if n == 0 {
		return
	}

	b.lastByte = -1
	b.lastRuneSize = -1

	remain := n
	for {
		skip := b.Buffered()
		if skip == 0 {
			b.fill()
			skip = b.Buffered()
		}
		if skip > remain {
			skip = remain
		}
		b.r += skip
		remain -= skip
		if remain == 0 {
			return n, nil
		}
		if b.err != nil {
			return n - remain, b.readErr()
		}
	}
}

// Read reads data into p.
// It returns the number of bytes read into p.
// The bytes are taken from at most one Read on the underlying Reader,
// hence n may be less than len(p).
// To read exactly len(p) bytes, use io.ReadFull(b, p).
// If the underlying Reader can return a non-zero count with io.EOF,
// then this Read method can do so as well; see the [io.Reader] docs.
// Read 读取数据放入p中，并返回读入到p中的字节数。
// 最多从底层的Reader读取一次，因为底层字节数可能会小于p的长度。
// 为了要准确读取len(p)的长度，请用io.ReadFull(b, p)。
// 如果底层的Reader能返回非零的字节数和io.EOF错误，那么Read方法能够做的更好；
// 具体见[io.Reader]的文档（译注：这个接口并没有强制Read的返回行为）。
func (b *Reader) Read(p []byte) (n int, err error) {
	n = len(p)
	if n == 0 {
		if b.Buffered() > 0 {
			return 0, nil
		}
		return 0, b.readErr()
	}
	if b.r == b.w {
		if b.err != nil {
			return 0, b.readErr()
		}
		if len(p) >= len(b.buf) {
			// Large read, empty buffer.
			// Read directly into p to avoid copy.
			n, b.err = b.rd.Read(p)
			if n < 0 {
				panic(errNegativeRead)
			}
			if n > 0 {
				b.lastByte = int(p[n-1])
				b.lastRuneSize = -1
			}
			return n, b.readErr()
		}
		// One read.
		// Do not use b.fill, which will loop.
		b.r = 0
		b.w = 0
		n, b.err = b.rd.Read(b.buf)
		if n < 0 {
			panic(errNegativeRead)
		}
		if n == 0 {
			return 0, b.readErr()
		}
		b.w += n
	}

	// copy as much as we can
	// Note: if the slice panics here, it is probably because
	// the underlying reader returned a bad count. See issue 49795.
	n = copy(p, b.buf[b.r:b.w])
	b.r += n
	b.lastByte = int(b.buf[b.r-1])
	b.lastRuneSize = -1
	return n, nil
}

// ReadByte reads and returns a single byte.
// If no byte is available, returns an error.
func (b *Reader) ReadByte() (byte, error) {
	b.lastRuneSize = -1
	for b.r == b.w {
		if b.err != nil {
			return 0, b.readErr()
		}
		b.fill() // buffer is empty
	}
	c := b.buf[b.r]
	b.r++
	b.lastByte = int(c)
	return c, nil
}

// UnreadByte unreads the last byte. Only the most recently read byte can be unread.
//
// UnreadByte returns an error if the most recent method called on the
// Reader was not a read operation. Notably, Peek, Discard, and WriteTo are not
// considered read operations.
func (b *Reader) UnreadByte() error {
	if b.lastByte < 0 || b.r == 0 && b.w > 0 {
		return ErrInvalidUnreadByte
	}
	// b.r > 0 || b.w == 0
	if b.r > 0 {
		b.r--
	} else {
		// b.r == 0 && b.w == 0
		b.w = 1
	}
	b.buf[b.r] = byte(b.lastByte)
	b.lastByte = -1
	b.lastRuneSize = -1
	return nil
}

// ReadRune reads a single UTF-8 encoded Unicode character and returns the
// rune and its size in bytes. If the encoded rune is invalid, it consumes one byte
// and returns unicode.ReplacementChar (U+FFFD) with a size of 1.
func (b *Reader) ReadRune() (r rune, size int, err error) {
	for b.r+utf8.UTFMax > b.w && !utf8.FullRune(b.buf[b.r:b.w]) && b.err == nil && b.w-b.r < len(b.buf) {
		b.fill() // b.w-b.r < len(buf) => buffer is not full
	}
	b.lastRuneSize = -1
	if b.r == b.w {
		return 0, 0, b.readErr()
	}
	r, size = rune(b.buf[b.r]), 1
	if r >= utf8.RuneSelf {
		r, size = utf8.DecodeRune(b.buf[b.r:b.w])
	}
	b.r += size
	b.lastByte = int(b.buf[b.r-1])
	b.lastRuneSize = size
	return r, size, nil
}

// UnreadRune unreads the last rune. If the most recent method called on
// the Reader was not a ReadRune, UnreadRune returns an error. (In this
// regard it is stricter than UnreadByte, which will unread the last byte
// from any read operation.)
func (b *Reader) UnreadRune() error {
	if b.lastRuneSize < 0 || b.r < b.lastRuneSize {
		return ErrInvalidUnreadRune
	}
	b.r -= b.lastRuneSize
	b.lastByte = -1
	b.lastRuneSize = -1
	return nil
}

// Buffered returns the number of bytes that can be read from the current buffer.
func (b *Reader) Buffered() int { return b.w - b.r }

// ReadSlice reads until the first occurrence of delim in the input,
// returning a slice pointing at the bytes in the buffer.
// The bytes stop being valid at the next read.
// If ReadSlice encounters an error before finding a delimiter,
// it returns all the data in the buffer and the error itself (often io.EOF).
// ReadSlice fails with error ErrBufferFull if the buffer fills without a delim.
// Because the data returned from ReadSlice will be overwritten
// by the next I/O operation, most clients should use
// ReadBytes or ReadString instead.
// ReadSlice returns err != nil if and only if line does not end in delim.
// ReadSlice 从输入读取字节直到指定的第一个delim出现，然后返回一个指向字节缓存的切片。
// 字节再下次读取时不再有效。
// 如果 ReadSlice 再找到定界符之前遇到了错误，它会返回所有数据和错误（通常是io.EOF）。
// 如果缓存中没有给定的定界符存在，那么ReadSlice将会返回错误ErrBufferFull。
// 因为返回的数据将会再下一次I/O操作时被覆盖（译注：因为返回的slice底层数组还是buffer），
// 大多数客户端应该使用ReadBytes或ReadString替代。
// ReadSlice 返回非nil错误当且仅当没有找到定界符。
func (b *Reader) ReadSlice(delim byte) (line []byte, err error) {
	s := 0 // search start index
	for {
		// Search buffer.
		if i := bytes.IndexByte(b.buf[b.r+s:b.w], delim); i >= 0 {
			i += s
			line = b.buf[b.r : b.r+i+1]
			b.r += i + 1
			break
		}

		// Pending error?
		if b.err != nil {
			line = b.buf[b.r:b.w]
			b.r = b.w
			err = b.readErr()
			break
		}

		// Buffer full?
		if b.Buffered() >= len(b.buf) {
			b.r = b.w
			line = b.buf
			err = ErrBufferFull
			break
		}

		// 即使后面b.fill改变了r和w，但是扫描过的区间大小不变
		s = b.w - b.r // do not rescan area we scanned before

		b.fill() // buffer is not full
	}

	// Handle last byte, if any.
	if i := len(line) - 1; i >= 0 {
		b.lastByte = int(line[i])
		b.lastRuneSize = -1
	}

	return
}

// ReadLine is a low-level line-reading primitive. Most callers should use
// ReadBytes('\n') or ReadString('\n') instead or use a Scanner.
// Readline 是一个低级别行读取原语。大多数的调用者都应该使用ReadBytes('\n')或ReadString('\n')
// 代替它或者使用Scanner。
//
// ReadLine tries to return a single line, not including the end-of-line bytes.
// If the line was too long for the buffer then isPrefix is set and the
// beginning of the line is returned. The rest of the line will be returned
// from future calls. isPrefix will be false when returning the last fragment
// of the line. The returned buffer is only valid until the next call to
// ReadLine. ReadLine either returns a non-nil line or it returns an error,
// never both.
// ReadLine 试图返回单行，不包括行尾字节（译注：即\r\n）。
// 如果该行对于缓冲区来说太长(译注：即读了缓冲区中的所有数据仍然没有到达行尾)，
// 则设置 isPrefix 为 true并且返回行的开头。 行剩下的部分将会再将来调用时返回。
// 当返回行的最后一个片段后isPrefix 将会被置为false。
//
// The text returned from ReadLine does not include the line end ("\r\n" or "\n").
// No indication or error is given if the input ends without a final line end.
// Calling UnreadByte after ReadLine will always unread the last byte read
// (possibly a character belonging to the line end) even if that byte is not
// part of the line returned by ReadLine.
// 从ReadLine返回的文本行不包含“\r\n”或"\n”。
// 如果输入在没有最后一行结束("\r\n" or "\n")的情况下结束，则不会给出任何指示或错误。
// 在 ReadLine 之后调用 UnreadByte 将始终unread已读取的最后一个字节（可能是属于行尾的字符），
// 即使该字节不是 ReadLine 返回的行的一部分。
func (b *Reader) ReadLine() (line []byte, isPrefix bool, err error) {
	line, err = b.ReadSlice('\n')
	if err == ErrBufferFull {
		// Handle the case where "\r\n" straddles the buffer.
		// 处理“\r\n”跨越缓冲区的情况。
		if len(line) > 0 && line[len(line)-1] == '\r' {
			// Put the '\r' back on buf and drop it from line.
			// Let the next call to ReadLine check for "\r\n".
			// 将 '\r' 放回 buf 并将其从行中删除。
			// 让下一次调用 ReadLine 检查“\r\n”。
			if b.r == 0 {
				// should be unreachable
				panic("bufio: tried to rewind past start of buffer")
			}
			b.r--
			line = line[:len(line)-1]
		}
		return line, true, nil
	}

	if len(line) == 0 {
		if err != nil {
			line = nil
		}
		return
	}
	err = nil

	if line[len(line)-1] == '\n' {
		drop := 1
		if len(line) > 1 && line[len(line)-2] == '\r' {
			drop = 2
		}
		line = line[:len(line)-drop]
	}
	return
}

// collectFragments reads until the first occurrence of delim in the input. It
// returns (slice of full buffers, remaining bytes before delim, total number
// of bytes in the combined first two elements, error).
// The complete result is equal to
// `bytes.Join(append(fullBuffers, finalFragment), nil)`, which has a
// length of `totalLen`. The result is structured in this way to allow callers
// to minimize allocations and copies.
func (b *Reader) collectFragments(delim byte) (fullBuffers [][]byte, finalFragment []byte, totalLen int, err error) {
	var frag []byte
	// Use ReadSlice to look for delim, accumulating full buffers.
	for {
		var e error
		frag, e = b.ReadSlice(delim)
		if e == nil { // got final fragment
			break
		}
		if e != ErrBufferFull { // unexpected error
			err = e
			break
		}

		// Make a copy of the buffer.
		buf := make([]byte, len(frag))
		copy(buf, frag)
		fullBuffers = append(fullBuffers, buf)
		totalLen += len(buf)
	}

	totalLen += len(frag)
	return fullBuffers, frag, totalLen, err
}

// ReadBytes reads until the first occurrence of delim in the input,
// returning a slice containing the data up to and including the delimiter.
// If ReadBytes encounters an error before finding a delimiter,
// it returns the data read before the error and the error itself (often io.EOF).
// ReadBytes returns err != nil if and only if the returned data does not end in
// delim.
// For simple uses, a Scanner may be more convenient.
// ReadBytes 读取直到输入中第一次出现delim，返回一个切片，其中包含直到并包括定界符的数据。
// 如果在找到定界符之前遇到了错误，ReadBytes返回已读取的数据和错误本身（通常是io.EOF）。
// ReadBytes 返回非nil错误当且仅当返回的数据没有以定界符结尾。
// 对于简单的使用，Scanner可能更方便。
func (b *Reader) ReadBytes(delim byte) ([]byte, error) {
	full, frag, n, err := b.collectFragments(delim)
	// Allocate new buffer to hold the full pieces and the fragment.
	buf := make([]byte, n)
	n = 0
	// Copy full pieces and fragment in.
	for i := range full {
		n += copy(buf[n:], full[i])
	}
	copy(buf[n:], frag)
	return buf, err
}

// ReadString reads until the first occurrence of delim in the input,
// returning a string containing the data up to and including the delimiter.
// If ReadString encounters an error before finding a delimiter,
// it returns the data read before the error and the error itself (often io.EOF).
// ReadString returns err != nil if and only if the returned data does not end in
// delim.
// For simple uses, a Scanner may be more convenient.
// ReadString 读取直到输入中第一次出现delim，返回一个字符串，其中包含定界符，如果有的话。
// 如果在找到定界符之前遇到了错误，ReadString返回已读取的数据和错误本身（通常是io.EOF）。
// ReadString 返回非nil错误当且仅当返回的数据没有以定界符结尾。
// 对于简单的使用，Scanner可能更方便一些。
func (b *Reader) ReadString(delim byte) (string, error) {
	full, frag, n, err := b.collectFragments(delim)
	// Allocate new buffer to hold the full pieces and the fragment.
	var buf strings.Builder
	buf.Grow(n)
	// Copy full pieces and fragment in.
	for _, fb := range full {
		buf.Write(fb)
	}
	buf.Write(frag)
	return buf.String(), err
}

// WriteTo implements io.WriterTo.
// This may make multiple calls to the Read method of the underlying Reader.
// If the underlying reader supports the WriteTo method,
// this calls the underlying WriteTo without buffering.
// WriteTo 实施了 io.WriterTo 接口。
// 它可能会多次调用底层Reader的Read方法。
// 如果底层reader支持WriteTo方法，将会直接调用底层的WriteTo方法而不需要缓存。
func (b *Reader) WriteTo(w io.Writer) (n int64, err error) {
	b.lastByte = -1
	b.lastRuneSize = -1

	n, err = b.writeBuf(w)
	if err != nil {
		return
	}

	if r, ok := b.rd.(io.WriterTo); ok {
		m, err := r.WriteTo(w)
		n += m
		return n, err
	}

	if w, ok := w.(io.ReaderFrom); ok {
		m, err := w.ReadFrom(b.rd)
		n += m
		return n, err
	}

	if b.w-b.r < len(b.buf) {
		b.fill() // buffer not full
	}

	for b.r < b.w {
		// b.r < b.w => buffer is not empty
		m, err := b.writeBuf(w)
		n += m
		if err != nil {
			return n, err
		}
		b.fill() // buffer is empty
	}

	if b.err == io.EOF {
		b.err = nil
	}

	return n, b.readErr()
}

var errNegativeWrite = errors.New("bufio: writer returned negative count from Write")

// writeBuf writes the Reader's buffer to the writer.
func (b *Reader) writeBuf(w io.Writer) (int64, error) {
	n, err := w.Write(b.buf[b.r:b.w])
	if n < 0 {
		panic(errNegativeWrite)
	}
	b.r += n
	return int64(n), err
}

// buffered output

// Writer implements buffering for an io.Writer object.
// If an error occurs writing to a Writer, no more data will be
// accepted and all subsequent writes, and Flush, will return the error.
// After all data has been written, the client should call the
// Flush method to guarantee all data has been forwarded to
// the underlying io.Writer.
// Writer 为io.Writer对象实现了缓存。
// 如果在向Writer写入时发生了错误，那么它将不再接受更多的数据，并且后续的写和Flush操作都将返回失败。
// 所有的数据都写入完成后，客户端应该调用Flush方法以确保所有的数据被写入到底层的io.Writer中。
type Writer struct {
	err error
	buf []byte
	n   int
	wr  io.Writer
}

// NewWriterSize returns a new Writer whose buffer has at least the specified
// size. If the argument io.Writer is already a Writer with large enough
// size, it returns the underlying Writer.
// NewWriterSize 返回一个Writer其缓存至少有指定的大小。
// 如果参数io.Writer是一个Writer且有足够大小的缓存，则直接返回w底层的Writer。
func NewWriterSize(w io.Writer, size int) *Writer {
	// Is it already a Writer?
	b, ok := w.(*Writer)
	if ok && len(b.buf) >= size {
		return b
	}
	if size <= 0 {
		size = defaultBufSize
	}
	return &Writer{
		buf: make([]byte, size),
		wr:  w,
	}
}

// NewWriter returns a new Writer whose buffer has the default size.
// If the argument io.Writer is already a Writer with large enough buffer size,
// it returns the underlying Writer.
func NewWriter(w io.Writer) *Writer {
	return NewWriterSize(w, defaultBufSize)
}

// Size returns the size of the underlying buffer in bytes.
func (b *Writer) Size() int { return len(b.buf) }

// Reset discards any unflushed buffered data, clears any error, and
// resets b to write its output to w.
// Calling Reset on the zero value of Writer initializes the internal buffer
// to the default size.
// Reset 丢弃缓存中还没有flush的数据，清除任何错误，并重置b以将其输入写入w。
// 在Writer的零值上（译注：应该是buf的零值，并发是对象为nil）调用Reset将会以默认的大小初始化内部缓存。
func (b *Writer) Reset(w io.Writer) {
	if b.buf == nil {
		b.buf = make([]byte, defaultBufSize)
	}
	b.err = nil
	b.n = 0
	b.wr = w
}

// Flush writes any buffered data to the underlying io.Writer.
// Flush 写任何已缓存的数据到底层的io.Writer。
func (b *Writer) Flush() error {
	if b.err != nil {
		return b.err
	}
	if b.n == 0 {
		return nil
	}
	n, err := b.wr.Write(b.buf[0:b.n])
	if n < b.n && err == nil {
		err = io.ErrShortWrite
	}
	if err != nil {
		if n > 0 && n < b.n {
			copy(b.buf[0:b.n-n], b.buf[n:b.n])
		}
		b.n -= n
		b.err = err
		return err
	}
	b.n = 0
	return nil
}

// Available returns how many bytes are unused in the buffer.
func (b *Writer) Available() int { return len(b.buf) - b.n }

// AvailableBuffer returns an empty buffer with b.Available() capacity.
// This buffer is intended to be appended to and
// passed to an immediately succeeding Write call.
// The buffer is only valid until the next write operation on b.
func (b *Writer) AvailableBuffer() []byte {
	return b.buf[b.n:][:0]
}

// Buffered returns the number of bytes that have been written into the current buffer.
func (b *Writer) Buffered() int { return b.n }

// Write writes the contents of p into the buffer.
// It returns the number of bytes written.
// If nn < len(p), it also returns an error explaining
// why the write is short.
// Write 把 p 的内容写入到缓存。
// 它返回写入的字节个数nn。
// 如果 nn 小于缓存的长度，必须返回一个错误来解释为什么没有全部写入。
func (b *Writer) Write(p []byte) (nn int, err error) {
	for len(p) > b.Available() && b.err == nil {
		var n int
		if b.Buffered() == 0 {
			// Large write, empty buffer.
			// Write directly from p to avoid copy.
			n, b.err = b.wr.Write(p)
		} else {
			n = copy(b.buf[b.n:], p)
			b.n += n
			b.Flush()
		}
		nn += n
		p = p[n:] // 如果n == len(p)，则p[n:]为[]
	}
	if b.err != nil {
		return nn, b.err
	}
	n := copy(b.buf[b.n:], p)
	b.n += n
	nn += n
	return nn, nil
}

// WriteByte writes a single byte.
func (b *Writer) WriteByte(c byte) error {
	if b.err != nil {
		return b.err
	}
	if b.Available() <= 0 && b.Flush() != nil {
		return b.err
	}
	b.buf[b.n] = c
	b.n++
	return nil
}

// WriteRune writes a single Unicode code point, returning
// the number of bytes written and any error.
func (b *Writer) WriteRune(r rune) (size int, err error) {
	// Compare as uint32 to correctly handle negative runes.
	if uint32(r) < utf8.RuneSelf {
		err = b.WriteByte(byte(r))
		if err != nil {
			return 0, err
		}
		return 1, nil
	}
	if b.err != nil {
		return 0, b.err
	}
	n := b.Available()
	if n < utf8.UTFMax {
		if b.Flush(); b.err != nil {
			return 0, b.err
		}
		n = b.Available()
		if n < utf8.UTFMax {
			// Can only happen if buffer is silly small.
			return b.WriteString(string(r))
		}
	}
	size = utf8.EncodeRune(b.buf[b.n:], r)
	b.n += size
	return size, nil
}

// WriteString writes a string.
// It returns the number of bytes written.
// If the count is less than len(s), it also returns an error explaining
// why the write is short.
func (b *Writer) WriteString(s string) (int, error) {
	var sw io.StringWriter
	tryStringWriter := true

	nn := 0
	for len(s) > b.Available() && b.err == nil {
		var n int
		if b.Buffered() == 0 && sw == nil && tryStringWriter {
			// Check at most once whether b.wr is a StringWriter.
			sw, tryStringWriter = b.wr.(io.StringWriter)
		}
		if b.Buffered() == 0 && tryStringWriter {
			// Large write, empty buffer, and the underlying writer supports
			// WriteString: forward the write to the underlying StringWriter.
			// This avoids an extra copy.
			n, b.err = sw.WriteString(s)
		} else {
			n = copy(b.buf[b.n:], s)
			b.n += n
			b.Flush()
		}
		nn += n
		s = s[n:]
	}
	if b.err != nil {
		return nn, b.err
	}
	n := copy(b.buf[b.n:], s)
	b.n += n
	nn += n
	return nn, nil
}

// ReadFrom implements io.ReaderFrom. If the underlying writer
// supports the ReadFrom method, this calls the underlying ReadFrom.
// If there is buffered data and an underlying ReadFrom, this fills
// the buffer and writes it before calling ReadFrom.
func (b *Writer) ReadFrom(r io.Reader) (n int64, err error) {
	if b.err != nil {
		return 0, b.err
	}
	readerFrom, readerFromOK := b.wr.(io.ReaderFrom)
	var m int
	for {
		if b.Available() == 0 {
			if err1 := b.Flush(); err1 != nil {
				return n, err1
			}
		}
		if readerFromOK && b.Buffered() == 0 {
			nn, err := readerFrom.ReadFrom(r)
			b.err = err
			n += nn
			return n, err
		}
		nr := 0
		for nr < maxConsecutiveEmptyReads {
			m, err = r.Read(b.buf[b.n:])
			if m != 0 || err != nil {
				break
			}
			nr++
		}
		if nr == maxConsecutiveEmptyReads {
			return n, io.ErrNoProgress
		}
		b.n += m
		n += int64(m)
		if err != nil {
			break
		}
	}
	if err == io.EOF {
		// If we filled the buffer exactly, flush preemptively.
		if b.Available() == 0 {
			err = b.Flush()
		} else {
			err = nil
		}
	}
	return n, err
}

// buffered input and output

// ReadWriter stores pointers to a Reader and a Writer.
// It implements io.ReadWriter.
type ReadWriter struct {
	*Reader
	*Writer
}

// NewReadWriter allocates a new ReadWriter that dispatches to r and w.
func NewReadWriter(r *Reader, w *Writer) *ReadWriter {
	return &ReadWriter{r, w}
}
