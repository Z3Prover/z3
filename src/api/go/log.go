// Copyright (c) Microsoft Corporation 2025
// Z3 Go API: Logging functionality

package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"sync"
	"unsafe"
)

var (
	logMutex  sync.Mutex
	isLogOpen bool
)

// OpenLog opens an interaction log file
// Returns true if successful, false otherwise
func OpenLog(filename string) bool {
	logMutex.Lock()
	defer logMutex.Unlock()
	
	cFilename := C.CString(filename)
	defer C.free(unsafe.Pointer(cFilename))
	
	result := C.Z3_open_log(cFilename)
	if bool(result) {
		isLogOpen = true
		return true
	}
	return false
}

// CloseLog closes the interaction log
func CloseLog() {
	logMutex.Lock()
	defer logMutex.Unlock()
	
	C.Z3_close_log()
	isLogOpen = false
}

// AppendLog appends a user-provided string to the interaction log
// Panics if the log is not open
func AppendLog(s string) {
	logMutex.Lock()
	defer logMutex.Unlock()
	
	if !isLogOpen {
		panic("Log is not open")
	}
	
	cStr := C.CString(s)
	defer C.free(unsafe.Pointer(cStr))
	C.Z3_append_log(cStr)
}

// IsLogOpen returns true if the interaction log is open
func IsLogOpen() bool {
	logMutex.Lock()
	defer logMutex.Unlock()
	return isLogOpen
}
