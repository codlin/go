// Copyright 2020 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package fs defines basic interfaces to a file system.
// A file system can be provided by the host operating system
// but also by other packages.
package fs

import (
	"internal/oserror"
	"time"
	"unicode/utf8"
)

// An FS provides access to a hierarchical file system.
// FS 提供了访问分层的文件系统。
//
// The FS interface is the minimum implementation required of the file system.
// A file system may implement additional interfaces,
// such as ReadFileFS, to provide additional or optimized functionality.
// FS 接口是文件系统所需的最小实现。
// 一个文件系统可以实施其它额外的接口，例如ReadFileFS，以通过额外的、优化的功能。
type FS interface {
	// Open opens the named file.
	//
	// When Open returns an error, it should be of type *PathError
	// with the Op field set to "open", the Path field set to name,
	// and the Err field describing the problem.
	// 当 Open 返回一个错误，它应是一个*PathError类型的错误，
	// 其中Op字段设置为'open'，Path字段设置为参数name，并且Err字段描述问题。
	//
	// Open should reject attempts to open names that do not satisfy
	// ValidPath(name), returning a *PathError with Err set to
	// ErrInvalid or ErrNotExist.
	// Open 应该拒绝尝试去打开不符合ValidPath(name)的文件，并返回一个*PathError
	// 错误，其Err字段被设置为ErrInvalid or ErrNotExist。
	Open(name string) (File, error)
}

// ValidPath reports whether the given path name
// is valid for use in a call to Open.
// ValidPath 报告给定的路径名在使用Open函数开始时是否是有效的名字。
//
// Path names passed to open are UTF-8-encoded,
// unrooted, slash-separated sequences of path elements, like “x/y/z”.
// Path names must not contain an element that is “.” or “..” or the empty string,
// except for the special case that the root directory is named “.”.
// Paths must not start or end with a slash: “/x” and “x/” are invalid.
// 路径名name是使用UTF-8编码、非root、斜杠隔开的路径，如“x/y/z”。
// 路径名name中禁止包含"."，".."或者为空字符串，但根路径"."除外（注：即代表当前路径的.)。
// 路径禁止以斜杠开始或结束，像“/x” 和 “x/”都是不合法的。
//
// Note that paths are slash-separated on all systems, even Windows.
// Paths containing other characters such as backslash and colon
// are accepted as valid, but those characters must never be
// interpreted by an FS implementation as path element separators.
// 需要注意的是路径在素有系统上都是以斜杠隔开的，哪怕是在Window上也是。
// 路径包含其它的字符例如反斜杠和分号是可以被合法接受的，但是FS的实施者绝不能将这些字符绝解释为
// 路径元素的分隔符。
func ValidPath(name string) bool {
	if !utf8.ValidString(name) {
		return false
	}

	if name == "." {
		// special case
		return true
	}

	// Iterate over elements in name, checking each.
	// 这段程序用来检查路径的合法性，按照斜杠取出其之前的元素，如果都合法则返回true，
	// 否则返回false。
	for {
		i := 0
		for i < len(name) && name[i] != '/' {
			i++
		}
		elem := name[:i]
		if elem == "" || elem == "." || elem == ".." {
			return false
		}
		if i == len(name) {
			return true // reached clean ending
		}
		name = name[i+1:]
	}
}

// A File provides access to a single file.
// The File interface is the minimum implementation required of the file.
// Directory files should also implement ReadDirFile.
// A file may implement io.ReaderAt or io.Seeker as optimizations.
//
// File 提供对单个文件的访问。
// File 接口是文件所需的最低实现。
// Directory 文件也应该实现 ReadDirFile。
// 一个文件可以实现 io.ReaderAt 或 io.Seeker 作为优化。
type File interface {
	Stat() (FileInfo, error)
	Read([]byte) (int, error)
	Close() error
}

// A DirEntry is an entry read from a directory
// (using the ReadDir function or a ReadDirFile's ReadDir method).
//
// DirEntry 是从目录中读取的一个条目entry。
// （使用 ReadDir 函数或 ReadDirFile 的 ReadDir 方法）
type DirEntry interface {
	// Name returns the name of the file (or subdirectory) described by the entry.
	// Name 返回条目entry描述的文件（或子目录）的名称。
	//
	// This name is only the final element of the path (the base name), not the entire path.
	// For example, Name would return "hello.go" not "home/gopher/hello.go".
	// 返回的这个名称仅仅是路径的最末端元素，而不是整个路径，如返回的是"hello.go"而不是"home/gopher/hello.go"。
	Name() string

	// IsDir reports whether the entry describes a directory.
	IsDir() bool

	// Type returns the type bits for the entry.
	// The type bits are a subset of the usual FileMode bits, those returned by the FileMode.Type method.
	//
	// Type 返回条目的类型位。
	// 这个类型位是常用的 FileMode 位的子集，这些位由 FileMode.Type 方法返回。
	Type() FileMode

	// Info returns the FileInfo for the file or subdirectory described by the entry.
	// Info 返回条目描述的文件或者子目录的FileInfo。
	//
	// The returned FileInfo may be from the time of the original directory read
	// or from the time of the call to Info. If the file has been removed or renamed
	// since the directory read, Info may return an error satisfying errors.Is(err, ErrNotExist).
	// 返回的 FileInfo 可能来自原始目录读取时（注：即ReadDir时）或调用 Info 时。如果文件在读取目录后已被删除或重命名，
	// Info 可能会返回一个满足 errors.Is(err, ErrNotExist) 的错误。
	//
	// If the entry denotes a symbolic link, Info reports the information about the link itself,
	// not the link's target.
	// 如果该条目表示符号链接，则 Info 报告有关链接本身的信息，而不是链接的目标。
	Info() (FileInfo, error)
}

// A ReadDirFile is a directory file whose entries can be read with the ReadDir method.
// Every directory file should implement this interface.
// (It is permissible for any file to implement this interface,
// but if so ReadDir should return an error for non-directories.)
//
// ReadDirFile 是一个目录文件，可以通过ReadDir方法读取它的各个条目entries。
// 所有目录文件都需要实施这个接口。
// (允许任何文件实现此接口，但如果是这样，ReadDir 应该为非目录返回错误。)
type ReadDirFile interface {
	File

	// ReadDir reads the contents of the directory and returns
	// a slice of up to n DirEntry values in directory order.
	// Subsequent calls on the same file will yield further DirEntry values.
	// ReadDir 读取目录的内容并且以目录的顺序返回最多n个DirEntry值的切片slice。
	// 对同一文件的后续调用将产生更多的 DirEntry 值。
	//
	// If n > 0, ReadDir returns at most n DirEntry structures.
	// In this case, if ReadDir returns an empty slice, it will return
	// a non-nil error explaining why.
	// At the end of a directory, the error is io.EOF.
	// (ReadDir must return io.EOF itself, not an error wrapping io.EOF.)
	// 如果n > 0，ReadDir 返回最多n个DirEntry结构。
	// 在这种情况下，如果 ReadDir 返回一个空切片，那么将返回一个非nil的错误解释其原因。
	// 如果到达了目录的末端，则返回io.EOF错误。
	// （ReadDir 必须返回io.EOF自身，而不是一个包装了io.EOF的错误。）
	//
	// If n <= 0, ReadDir returns all the DirEntry values from the directory
	// in a single slice. In this case, if ReadDir succeeds (reads all the way
	// to the end of the directory), it returns the slice and a nil error.
	// If it encounters an error before the end of the directory,
	// ReadDir returns the DirEntry list read until that point and a non-nil error.
	// 如果n <= 0，ReadDir 在一个slice里返回目录下的所有DirEntry值。在这种情况下，
	// 如果ReadDir成功（一路读取到了目录末尾），它将返回slice和一个nil错误。
	// 如果它在到达目录末尾之前遇到了错误，ReadDir返回已读取的DirEntry列表和一个非nil错误。
	ReadDir(n int) ([]DirEntry, error)
}

// Generic file system errors.
// Errors returned by file systems can be tested against these errors
// using errors.Is.
var (
	ErrInvalid    = errInvalid()    // "invalid argument"
	ErrPermission = errPermission() // "permission denied"
	ErrExist      = errExist()      // "file already exists"
	ErrNotExist   = errNotExist()   // "file does not exist"
	ErrClosed     = errClosed()     // "file already closed"
)

func errInvalid() error    { return oserror.ErrInvalid }
func errPermission() error { return oserror.ErrPermission }
func errExist() error      { return oserror.ErrExist }
func errNotExist() error   { return oserror.ErrNotExist }
func errClosed() error     { return oserror.ErrClosed }

// A FileInfo describes a file and is returned by Stat.
// FileInfo 用来描述一个文件并由函数Stat返回。
type FileInfo interface {
	Name() string       // base name of the file
	Size() int64        // length in bytes for regular files; system-dependent for others
	Mode() FileMode     // file mode bits
	ModTime() time.Time // modification time
	IsDir() bool        // abbreviation for Mode().IsDir()
	Sys() any           // underlying data source (can return nil)
}

// A FileMode represents a file's mode and permission bits.
// The bits have the same definition on all systems, so that
// information about files can be moved from one system
// to another portably. Not all bits apply to all systems.
// The only required bit is ModeDir for directories.
// FileMode 表示文件的模式和权限位。
// 这些位在所有系统上都有相同的定义，因此有关文件的信息可以从一个系统移植到另一个系统。
// 并非所有位都适用于所有系统。目录唯一需要的位是 ModeDir。
type FileMode uint32

// The defined file mode bits are the most significant bits of the FileMode.
// 定义的文件模式位是 FileMode 的最高有效位。
//
// The nine least-significant bits are the standard Unix rwxrwxrwx permissions.
// 九个最低有效位是标准的 Unix rwxrwxrwx 权限。
//
// The values of these bits should be considered part of the public API and
// may be used in wire protocols or disk representations: they must not be
// changed, although new bits might be added.
// 这些位的值应被视为公共 API 的一部分，并可用于有线协议或磁盘表示：它们不得更改，但可能会添加新位。
// wire protocols: https://en.wikipedia.org/wiki/Wire_protocol
const (
	// The single letters are the abbreviations
	// used by the String method's formatting.
	ModeDir        FileMode = 1 << (32 - 1 - iota) // d: is a directory
	ModeAppend                                     // a: append-only
	ModeExclusive                                  // l: exclusive use
	ModeTemporary                                  // T: temporary file; Plan 9 only
	ModeSymlink                                    // L: symbolic link
	ModeDevice                                     // D: device file
	ModeNamedPipe                                  // p: named pipe (FIFO)
	ModeSocket                                     // S: Unix domain socket
	ModeSetuid                                     // u: setuid
	ModeSetgid                                     // g: setgid
	ModeCharDevice                                 // c: Unix character device, when ModeDevice is set
	ModeSticky                                     // t: sticky
	ModeIrregular                                  // ?: non-regular file; nothing else is known about this file

	// Mask for the type bits. For regular files, none will be set.
	ModeType = ModeDir | ModeSymlink | ModeNamedPipe | ModeSocket | ModeDevice | ModeCharDevice | ModeIrregular

	ModePerm FileMode = 0777 // Unix permission bits
)

func (m FileMode) String() string {
	const str = "dalTLDpSugct?"
	var buf [32]byte // Mode is uint32.
	w := 0
	for i, c := range str {
		if m&(1<<uint(32-1-i)) != 0 {
			buf[w] = byte(c)
			w++
		}
	}
	if w == 0 {
		buf[w] = '-'
		w++
	}
	const rwx = "rwxrwxrwx"
	for i, c := range rwx {
		if m&(1<<uint(9-1-i)) != 0 {
			buf[w] = byte(c)
		} else {
			buf[w] = '-'
		}
		w++
	}
	return string(buf[:w])
}

// IsDir reports whether m describes a directory.
// That is, it tests for the ModeDir bit being set in m.
func (m FileMode) IsDir() bool {
	return m&ModeDir != 0
}

// IsRegular reports whether m describes a regular file.
// That is, it tests that no mode type bits are set.
func (m FileMode) IsRegular() bool {
	return m&ModeType == 0
}

// Perm returns the Unix permission bits in m (m & ModePerm).
func (m FileMode) Perm() FileMode {
	return m & ModePerm
}

// Type returns type bits in m (m & ModeType).
func (m FileMode) Type() FileMode {
	return m & ModeType
}

// PathError records an error and the operation and file path that caused it.
type PathError struct {
	Op   string
	Path string
	Err  error
}

func (e *PathError) Error() string { return e.Op + " " + e.Path + ": " + e.Err.Error() }

func (e *PathError) Unwrap() error { return e.Err }

// Timeout reports whether this error represents a timeout.
func (e *PathError) Timeout() bool {
	t, ok := e.Err.(interface{ Timeout() bool })
	return ok && t.Timeout()
}
