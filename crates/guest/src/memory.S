.option push
.option norvc
.option norelax

.section .text.memcpy,"ax",@progbits
.globl memcpy
.type memcpy,@function
.balign 4
memcpy:
    mv t0, a0
    li t1, 8
.Lcopy_words:
    bltu a2, t1, .Lcopy_bytes
    ld t2, 0(a1)
    sd t2, 0(t0)
    addi a1, a1, 8
    addi t0, t0, 8
    addi a2, a2, -8
    j .Lcopy_words
.Lcopy_bytes:
    beqz a2, .Lcopy_done
    lbu t2, 0(a1)
    sb t2, 0(t0)
    addi a1, a1, 1
    addi t0, t0, 1
    addi a2, a2, -1
    j .Lcopy_bytes
.Lcopy_done:
    ret
.size memcpy, . - memcpy

.section .text.memcmp,"ax",@progbits
.globl memcmp
.type memcmp,@function
.balign 4
memcmp:
    beqz a2, .Lcompare_equal
    lbu t1, 0(a0)
    lbu t2, 0(a1)
    bne t1, t2, .Lcompare_different
    li t0, 1
    beq a2, t0, .Lcompare_equal
    lbu t1, 1(a0)
    lbu t2, 1(a1)
    bne t1, t2, .Lcompare_different
    li t0, 8
.Lcompare_words:
    bltu a2, t0, .Lcompare_bytes
    ld t1, 0(a0)
    ld t2, 0(a1)
    bne t1, t2, .Lcompare_bytes
    addi a0, a0, 8
    addi a1, a1, 8
    addi a2, a2, -8
    j .Lcompare_words
.Lcompare_bytes:
    beqz a2, .Lcompare_equal
    lbu t1, 0(a0)
    lbu t2, 0(a1)
    bne t1, t2, .Lcompare_different
    addi a0, a0, 1
    addi a1, a1, 1
    addi a2, a2, -1
    j .Lcompare_bytes
.Lcompare_equal:
    li a0, 0
    ret
.Lcompare_different:
    sub a0, t1, t2
    ret
.size memcmp, . - memcmp

.option pop
