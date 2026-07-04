#
# Blaise — An Object Pascal Compiler
# Copyright (c) 2026 Graeme Geldenhuys
# SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
# Licensed under the Apache License v2.0 with Runtime Library Exception.
# See LICENSE file in the project root for full license terms.
#
# Atomic 32-bit integer operations for ARC thread safety (x86_64).
#
# These use the x86 LOCK prefix for full sequential-consistency
# atomics.  LOCK XADD atomically adds a value to a memory location
# and returns the previous value in the source register.
#

.text

# function _AtomicAddInt32(Ptr: PInteger; Delta: Integer): Integer;
#   %rdi = pointer to 32-bit integer
#   %esi = value to add
#   Returns the value BEFORE the addition.
.globl _AtomicAddInt32
.type  _AtomicAddInt32, @function
_AtomicAddInt32:
    movl %esi, %eax
    lock xaddl %eax, (%rdi)
    ret
.size _AtomicAddInt32, .-_AtomicAddInt32


# function _AtomicSubInt32(Ptr: PInteger; Delta: Integer): Integer;
#   %rdi = pointer to 32-bit integer
#   %esi = value to subtract
#   Returns the value BEFORE the subtraction.
.globl _AtomicSubInt32
.type  _AtomicSubInt32, @function
_AtomicSubInt32:
    negl %esi
    movl %esi, %eax
    lock xaddl %eax, (%rdi)
    ret
.size _AtomicSubInt32, .-_AtomicSubInt32


.section .note.GNU-stack,"",@progbits
