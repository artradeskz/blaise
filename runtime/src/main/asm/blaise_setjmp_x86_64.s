#
# Blaise — An Object Pascal Compiler
# Copyright (c) 2026 Graeme Geldenhuys
# SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
# Licensed under the Apache License v2.0 with Runtime Library Exception.
# See LICENSE file in the project root for full license terms.
#
# Minimal setjmp/longjmp for Blaise exception handling (x86_64, System V ABI).
#
# These replace libc setjmp/longjmp so the runtime has zero C dependencies
# for exception dispatch.  Only callee-saved registers are stored — this is
# sufficient because the compiler never promotes locals across setjmp (all
# locals in try-bearing functions remain as stack slots).
#
# jmp_buf layout (64 bytes at offset 0 of BlaiseExcFrame):
#   [0]  RBX
#   [8]  RBP
#   [16] R12
#   [24] R13
#   [32] R14
#   [40] R15
#   [48] RSP  (caller's stack pointer, after return address)
#   [56] RIP  (return address)
#

.text

# int _blaise_setjmp(void *buf)
#   %rdi = pointer to jmp_buf (first 64 bytes of BlaiseExcFrame)
#   Returns 0 on direct call, non-zero when restored by _blaise_longjmp.
.globl _blaise_setjmp
.type  _blaise_setjmp, @function
_blaise_setjmp:
    mov  %rbx,    (%rdi)
    mov  %rbp,   8(%rdi)
    mov  %r12,  16(%rdi)
    mov  %r13,  24(%rdi)
    mov  %r14,  32(%rdi)
    mov  %r15,  40(%rdi)
    lea  8(%rsp), %rax          # caller's RSP (skip the return address)
    mov  %rax,  48(%rdi)
    mov  (%rsp), %rax           # return address
    mov  %rax,  56(%rdi)
    xor  %eax, %eax             # return 0
    ret
.size _blaise_setjmp, .-_blaise_setjmp


# void _blaise_longjmp(void *buf, int val)
#   %rdi = pointer to jmp_buf
#   %esi = return value (passed back through setjmp's return)
#   Does not return to caller — jumps to the setjmp call site.
.globl _blaise_longjmp
.type  _blaise_longjmp, @function
_blaise_longjmp:
    mov  %esi, %eax             # return value
    test %eax, %eax
    jnz  1f
    inc  %eax                   # longjmp(buf, 0) must return 1
1:
    mov    (%rdi), %rbx
    mov   8(%rdi), %rbp
    mov  16(%rdi), %r12
    mov  24(%rdi), %r13
    mov  32(%rdi), %r14
    mov  40(%rdi), %r15
    mov  48(%rdi), %rsp
    jmp *56(%rdi)               # jump to saved return address
.size _blaise_longjmp, .-_blaise_longjmp


.section .note.GNU-stack,"",@progbits
