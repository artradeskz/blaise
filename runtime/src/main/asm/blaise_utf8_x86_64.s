#
# Blaise — An Object Pascal Compiler
# Copyright (c) 2026 Graeme Geldenhuys
# SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
# Licensed under the Apache License v2.0 with Runtime Library Exception.
# See LICENSE file in the project root for full license terms.
#
# SIMD-accelerated UTF-8 codepoint counting (x86_64).
#
# _Utf8CountCodePoints counts the number of UTF-8 codepoints in a byte buffer
# by counting non-continuation bytes (bytes where (b & 0xC0) != 0x80).
#
# Strategy: use AVX2 (32 bytes/iteration) when available, fall back to SSE2
# (16 bytes/iteration), then scalar for tail bytes.
#
# Calling convention (System V AMD64):
#   %rdi = pointer to first byte of string data
#   %esi = byte length of the string
#   Returns codepoint count in %eax.
#

.text

.globl _Utf8CountCodePoints
.type  _Utf8CountCodePoints, @function
_Utf8CountCodePoints:
    # Fast path: empty or very short strings
    testl %esi, %esi
    jle .Lreturn_zero

    movl %esi, %ecx            # ecx = remaining bytes
    xorl %eax, %eax            # eax = codepoint count accumulator
    xorl %edx, %edx            # edx = current offset

    # Check for AVX2 support via CPUID (cached in .Lavx2_flag)
    cmpl $0, .Lavx2_checked(%rip)
    jne .Lavx2_known
    call .Lcheck_avx2
    xorl %eax, %eax            # restore accumulator (cpuid clobbers eax)
.Lavx2_known:
    cmpl $0, .Lavx2_flag(%rip)
    je .Lsse2_entry

    # --- AVX2 path: 32 bytes per iteration ---
    cmpl $32, %ecx
    jb .Lsse2_entry

    # 0x80 broadcast into ymm1 (continuation byte marker)
    vpcmpeqb %ymm2, %ymm2, %ymm2   # ymm2 = all 0xFF
    vpsrlw $1, %ymm2, %ymm2         # ymm2 = 0x7F7F...
    vpaddw %ymm2, %ymm2, %ymm1      # This doesn't give 0x80 correctly
    # Correct approach: use vpbroadcastb-equivalent via stack
    # Actually: 0x80 = set top bit of each byte
    vpcmpeqb %ymm2, %ymm2, %ymm2   # ymm2 = all 0xFF
    vpsllw $7, %ymm2, %ymm1         # ymm1 = 0x80 in each byte position
    # That gives 0x80,0x00 pattern in words. Need per-byte.
    # Use vpabsb on all-ones to get 0x01, then shift.
    # Simplest: build 0xC0 and 0x80 masks on stack.

    # Better: count bytes where (byte & 0xC0) != 0x80
    # Equivalent: count bytes where byte < 0x80 OR byte >= 0xC0
    # Which is: NOT a continuation byte (10xxxxxx pattern)
    # A continuation byte has bits 7:6 == 10.
    # (byte + 0x40) sets bit 7 for 0x80..0xBF range → overflow into 0xC0..0xFF
    # Then test bit 7: if set = NOT continuation.
    # Actually simplest SIMD approach: byte >= 0xC0 OR byte < 0x80
    # = saturating subtract 0x80, then compare > 0x3F (catches >= 0xC0)
    #   OR original byte < 0x80
    # Even simpler: (byte & 0xC0) != 0x80
    # → XOR with 0x80 → (byte ^ 0x80) & 0xC0 != 0 iff not continuation
    # → shift right by 6 and sum? No.
    #
    # Standard trick: count bytes that are NOT 10xxxxxx.
    # A byte is a lead/ASCII byte iff its top two bits are NOT 10.
    # pcmpgtb is signed comparison, so:
    #   (signed) byte > -65 (0xBF as signed = -65) means byte >= 0xC0
    #   (signed) byte > -1 means byte >= 0 means byte < 0x80 (ASCII)... no.
    #
    # Classic UTF-8 SIMD count:
    #   For each byte B: is_not_continuation = ((B & 0xC0) != 0x80)
    #   Using signed arithmetic:
    #     Treat bytes as signed: continuation bytes 0x80..0xBF = -128..-65
    #     if (signed_byte > -65) → NOT continuation (includes 0xC0..0xFF and 0x00..0x7F)
    #     pcmpgtb ymm_data, ymm_threshold(-65) → 0xFF for non-continuation bytes
    #
    # Wait — pcmpgtb(a, b) = a > b? No: pcmpgtb dest, src means dest[i] = (dest[i] > src[i]) ? 0xFF : 0x00
    # We want: data[i] > -65  → is_not_continuation
    # So we need pcmpgtb with data in dest and -65 broadcast in src.
    # But pcmpgtb is destructive. So:
    #   1. Load data into ymm0
    #   2. Set ymm1 = broadcast(-65) = 0xBF bytes
    #   3. vpcmpgtb ymm2, ymm0, ymm1  → ymm2[i] = 0xFF if data[i] > -65 (signed)
    #   4. vpsrlw $7 on result... no, we need to count the 0xFF bytes.
    #   5. Sum: vpsubb zeros, ymm2 (subtracting 0xFF = adding 1 per set byte)
    #      Actually -(-1) = 1, so vpsubb(0, mask) counts ones.
    #   But vpsubb has no immediate form; use pabsb on the result (abs(-1)=1, abs(0)=0)
    #      vpsabsb ymm2, ymm2 → each byte is 0 or 1
    #   6. vpsadbw to horizontally sum bytes → 4 x 16-bit sums in qword lanes

    # Build threshold: broadcast -65 (0xBF as signed) into ymm1
    # -65 = 0xBF. All bytes 0xBF.
    vpcmpeqb %ymm1, %ymm1, %ymm1   # ymm1 = all 0xFF
    # We need 0xBF = ~0x40. Start from 0xFF, add 0xC0? No.
    # 0xBF = 0xFF - 0x40. Use vpaddb with -0x40? We don't have that.
    # Simplest: load from memory constant.
    vmovdqa .Lthreshold_avx(%rip), %ymm1

    vpxor %ymm3, %ymm3, %ymm3      # ymm3 = zero (accumulator)

.Lavx2_loop:
    vmovdqu (%rdi, %rdx), %ymm0    # load 32 bytes
    vpcmpgtb %ymm1, %ymm0, %ymm2   # ymm2[i] = 0xFF if data[i] > -65 (signed)
    vpabsb %ymm2, %ymm2            # ymm2[i] = 0 or 1
    vpaddb %ymm2, %ymm3, %ymm3     # accumulate byte counts (safe for 255 iters)

    addl $32, %edx
    subl $32, %ecx
    cmpl $32, %ecx
    jge .Lavx2_loop

    # Horizontal sum of ymm3: vpsadbw → sum each 8-byte lane into 64-bit
    vpxor %ymm4, %ymm4, %ymm4
    vpsadbw %ymm4, %ymm3, %ymm3    # ymm3 = 4 x 64-bit partial sums
    # Extract and sum the 4 quadwords
    vextracti128 $1, %ymm3, %xmm4
    vpaddq %xmm4, %xmm3, %xmm3    # xmm3 = 2 x 64-bit sums
    vpshufd $0x0E, %xmm3, %xmm4   # move high qword to low
    vpaddq %xmm4, %xmm3, %xmm3
    vmovd %xmm3, %r8d
    addl %r8d, %eax

    vzeroupper
    jmp .Lsse2_entry

    # --- SSE2 path: 16 bytes per iteration ---
.Lsse2_entry:
    cmpl $16, %ecx
    jb .Lscalar_entry

    # Build threshold -65 (0xBF) in xmm1
    movdqa .Lthreshold_sse(%rip), %xmm1
    pxor %xmm3, %xmm3              # xmm3 = zero accumulator

.Lsse2_loop:
    movdqu (%rdi, %rdx), %xmm0     # load 16 bytes
    movdqa %xmm0, %xmm2            # copy (pcmpgtb is destructive)
    pcmpgtb %xmm1, %xmm2           # xmm2[i] = 0xFF if data[i] > -65
    pabsb %xmm2, %xmm2             # xmm2[i] = 0 or 1
    paddb %xmm2, %xmm3             # accumulate (safe for 255 iters)

    addl $16, %edx
    subl $16, %ecx
    cmpl $16, %ecx
    jge .Lsse2_loop

    # Horizontal sum of xmm3
    pxor %xmm4, %xmm4
    psadbw %xmm4, %xmm3            # xmm3 = 2 x 64-bit sums
    movd %xmm3, %r8d
    pshufd $0x0E, %xmm3, %xmm3
    movd %xmm3, %r9d
    addl %r8d, %eax
    addl %r9d, %eax

    # --- Scalar tail: remaining < 16 bytes ---
.Lscalar_entry:
    testl %ecx, %ecx
    jle .Lreturn

.Lscalar_loop:
    movzbl (%rdi, %rdx), %r8d      # load one byte
    # Non-continuation if (byte & 0xC0) != 0x80
    movl %r8d, %r9d
    andl $0xC0, %r9d
    cmpl $0x80, %r9d
    setne %r9b
    movzbl %r9b, %r9d
    addl %r9d, %eax
    incl %edx
    decl %ecx
    jnz .Lscalar_loop

.Lreturn:
    ret

.Lreturn_zero:
    xorl %eax, %eax
    ret

# --- AVX2 detection subroutine ---
.Lcheck_avx2:
    pushq %rbx
    pushq %rcx
    pushq %rdx
    # CPUID leaf 7, subleaf 0 — bit 5 of EBX = AVX2
    movl $7, %eax
    xorl %ecx, %ecx
    cpuid
    testl $(1 << 5), %ebx
    setne %al
    movzbl %al, %eax
    movl %eax, .Lavx2_flag(%rip)
    movl $1, .Lavx2_checked(%rip)
    popq %rdx
    popq %rcx
    popq %rbx
    ret

.size _Utf8CountCodePoints, .-_Utf8CountCodePoints


# --- Read-only data (threshold constant) ---
.section .rodata
.balign 32
.Lthreshold_avx:
    .fill 32, 1, 0xBF
.balign 16
.Lthreshold_sse:
    .fill 16, 1, 0xBF

# --- Mutable data (AVX2 detection cache) ---
.section .data
.Lavx2_checked:
    .long 0
.Lavx2_flag:
    .long 0
