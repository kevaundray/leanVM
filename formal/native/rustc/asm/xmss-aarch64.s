	.file	"xmss.e3b090c1caa48f6d-cgu.0"
	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	2
	.type	memcpy,@function
memcpy:
.Lfunc_begin0:
	.cfi_startproc
	orr	w8, w1, w0
	orr	w8, w8, w2
	tst	x8, #0x7
	b.eq	.LBB0_4
	cbz	x2, .LBB0_7
	mov	x8, x0
.LBB0_3:
	ldrb	w9, [x1], #1
	subs	x2, x2, #1
	strb	w9, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB0_3
	b	.LBB0_7
.LBB0_4:
	cbz	x2, .LBB0_7
	mov	x8, xzr
.LBB0_6:
	ldr	x9, [x1, x8]
	str	x9, [x0, x8]
	add	x8, x8, #8
	//APP
	//NO_APP
	cmp	x8, x2
	b.lo	.LBB0_6
.LBB0_7:
	ret
.Lfunc_end0:
	.size	memcpy, .Lfunc_end0-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	2
	.type	memset,@function
memset:
.Lfunc_begin1:
	.cfi_startproc
	orr	w8, w2, w0
	tst	x8, #0x7
	b.eq	.LBB1_4
	cbz	x2, .LBB1_7
	mov	x8, x0
.LBB1_3:
	subs	x2, x2, #1
	strb	w1, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB1_3
	b	.LBB1_7
.LBB1_4:
	cbz	x2, .LBB1_7
	and	w8, w1, #0xff
	mov	x9, #72340172838076673
	mul	x8, x8, x9
	mov	x9, xzr
.LBB1_6:
	str	x8, [x0, x9]
	add	x9, x9, #8
	//APP
	//NO_APP
	cmp	x9, x2
	b.lo	.LBB1_6
.LBB1_7:
	ret
.Lfunc_end1:
	.size	memset, .Lfunc_end1-memset
	.cfi_endproc

	.section	.text.xmss_verify,"ax",@progbits
	.globl	xmss_verify
	.p2align	2
	.type	xmss_verify,@function
xmss_verify:
.Lfunc_begin2:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	mov	x29, sp
	.cfi_def_cfa w29, 96
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	sub	sp, sp, #1680
	add	x22, sp, #44
	ldr	xzr, [sp]
	mov	x20, x0
	add	x21, sp, #1, lsl #12
	add	x0, x22, #4
	mov	w1, wzr
	mov	w2, #2400
	add	x21, x21, #1296
	add	x19, x22, #4
	bl	memset
	ldr	x8, [x20, #1056]
	ldr	x9, [x20, #1064]
	add	x12, x22, #20
	ldr	x10, [x20, #1072]
	ldr	x13, [x20, #1080]
	mov	w14, #300
	ldr	x24, [x20, #1088]
	stp	x8, x9, [sp, #8]
	ldr	x8, [x20, #1024]
	ldr	x9, [x20, #1032]
	stp	x10, x13, [sp, #24]
	add	x13, x20, #1120
	ldr	x10, [x20, #1040]
	mov	w23, w24
	ldr	x11, [x20, #1048]
	str	w24, [sp, #44]
.LBB2_1:
	ldp	x15, x16, [x13, #-24]
	subs	x14, x14, #4
	stp	x15, x16, [x12, #-16]
	ldp	x15, x17, [x13, #-8]
	add	x13, x13, #32
	stp	x15, x17, [x12], #32
	b.ne	.LBB2_1
	add	x1, sp, #1, lsl #12
	str	x8, [sp, #2448]
	mov	w8, #2400
	add	x0, sp, #2492
	add	x1, x1, #1312
	str	x9, [sp, #2456]
	str	x10, [sp, #2464]
	add	x20, sp, #2448
	str	x11, [sp, #2472]
	str	x19, [sp, #5408]
	add	x19, sp, #2492
	str	x8, [sp, #5416]
	bl	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	add	x1, sp, #1, lsl #12
	add	x0, x19, #1200
	add	x22, x19, #1200
	add	x1, x1, #1312
	bl	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	add	x0, sp, #1, lsl #12
	add	x1, x20, #16
	add	x4, sp, #8
	add	x0, x0, #1312
	add	x6, x19, #1184
	add	x7, x19, #256
	mov	x2, xzr
	mov	w3, w24
	mov	w5, #32
	str	w24, [sp, #4892]
	bl	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	ldrb	w8, [x21, #16]
	cbz	w8, .LBB2_9
	ldur	x8, [x21, #81]
	ldurh	w9, [x21, #89]
	add	x25, sp, #1, lsl #12
	ldur	x10, [x21, #49]
	add	x26, sp, #1, lsl #12
	add	x19, sp, #1, lsl #12
	str	x8, [sp, #4960]
	ldur	x8, [x21, #57]
	add	x25, x25, #800
	strh	w9, [sp, #4968]
	ldur	x9, [x21, #65]
	add	x26, x26, #920
	str	x8, [sp, #4936]
	ldur	x8, [x21, #73]
	add	x27, sp, #2492
	str	x10, [sp, #4928]
	ldur	x10, [x21, #17]
	mov	w28, #1
	str	x8, [sp, #4952]
	ldur	x8, [x21, #25]
	add	x19, x19, #880
	str	x9, [sp, #4944]
	ldur	x9, [x21, #33]
	mov	w20, #3
	str	x8, [sp, #4904]
	ldur	x8, [x21, #41]
	str	x24, [sp]
	mov	x24, xzr
	str	x10, [sp, #4896]
	str	x9, [sp, #4912]
	str	x8, [sp, #4920]
.LBB2_4:
	lsl	x9, x28, x24
	ldur	x8, [x25, #58]
	ldur	x10, [x25, #66]
	add	x24, x24, #1
	add	x0, sp, #1, lsl #12
	mov	w1, wzr
	tst	x9, x23
	str	x8, [sp, #4976]
	lsr	x8, x23, x24
	str	x10, [sp, #4984]
	csel	x9, x19, x27, eq
	add	x0, x0, #1312
	ldp	x10, x9, [x9]
	str	w8, [sp, #5392]
	csel	x8, x27, x19, eq
	mov	w2, #344
	strh	w24, [sp, #5396]
	strb	w20, [x21, #7]
	str	x10, [sp, #5016]
	ldp	x10, x8, [x8]
	str	x9, [sp, #5024]
	lsr	w9, w24, #16
	str	xzr, [sp, #5400]
	stp	x10, x8, [x26, #16]
	strb	w9, [x21, #6]
	bl	memset
	add	x0, sp, #1, lsl #12
	add	x8, sp, #2448
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x8, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x1, #1296
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #344
	add	x0, x0, #952
	add	x1, x1, #1312
	bl	memcpy
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #32
	add	x0, x0, #952
	add	x1, x1, #920
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	add	x0, x0, #1312
	add	x1, x1, #952
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #5408]
	ldr	x9, [sp, #5416]
	cmp	x24, #16
	add	x27, x27, #16
	stur	x8, [x25, #58]
	stur	x9, [x25, #66]
	b.ne	.LBB2_4
	ldr	x8, [sp]
	add	x0, sp, #1, lsl #12
	add	x9, sp, #2448
	add	x0, x0, #1312
	add	x1, x9, #16
	add	x4, x25, #58
	lsr	w19, w8, #16
	add	x8, sp, #2492
	mov	w2, #1
	add	x6, x8, #2384
	add	x7, x8, #1456
	mov	w5, #16
	mov	w3, w19
	bl	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	ldrb	w8, [x21, #16]
	add	x27, sp, #2448
	cbz	w8, .LBB2_9
	ldur	x8, [x21, #83]
	ldur	x9, [x21, #75]
	add	x23, sp, #1, lsl #12
	add	x25, sp, #1, lsl #12
	add	x23, x23, #920
	mov	w24, #1
	add	x25, x25, #880
	mov	w26, #3
	mov	w20, #1
.LBB2_7:
	sub	x10, x20, #1
	str	x9, [sp, #4976]
	lsr	x11, x19, x20
	lsl	x10, x24, x10
	str	x8, [sp, #4984]
	add	x0, sp, #1, lsl #12
	add	x0, x0, #1312
	mov	w1, wzr
	mov	w2, #344
	tst	x10, x19
	orr	w10, w20, #0x800000
	str	w11, [sp, #5392]
	csel	x9, x25, x22, eq
	lsr	w8, w10, #16
	strh	w20, [sp, #5396]
	ldp	x10, x9, [x9]
	strb	w26, [x21, #7]
	strb	w8, [x21, #6]
	csel	x8, x22, x25, eq
	str	xzr, [sp, #5400]
	str	x10, [sp, #5016]
	ldp	x10, x8, [x8]
	str	x9, [sp, #5024]
	stp	x10, x8, [x23, #16]
	bl	memset
	add	x0, sp, #1, lsl #12
	add	x1, x27, #16
	mov	w2, #16
	add	x0, x0, #1312
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x1, #1296
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #344
	add	x0, x0, #952
	add	x1, x1, #1312
	bl	memcpy
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #32
	add	x0, x0, #952
	add	x1, x1, #920
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	add	x0, x0, #1312
	add	x1, x1, #952
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	add	x20, x20, #1
	ldr	x8, [sp, #5416]
	ldr	x9, [sp, #5408]
	cmp	x20, #17
	add	x22, x22, #16
	b.ne	.LBB2_7
	ldr	x10, [sp, #2448]
	ldr	x11, [sp, #2456]
	cmp	x9, x10
	ccmp	x8, x11, #0, eq
	cset	w0, eq
	b	.LBB2_10
.LBB2_9:
	mov	x0, xzr
.LBB2_10:
	add	sp, sp, #1, lsl #12
	add	sp, sp, #1680
	.cfi_def_cfa wsp, 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end2:
	.size	xmss_verify, .Lfunc_end2-xmss_verify
	.cfi_endproc

	.section	.text._RNvCsndc0WgnAaH_9keccak2568keccak_f,"ax",@progbits
	.p2align	2
	.type	_RNvCsndc0WgnAaH_9keccak2568keccak_f,@function
_RNvCsndc0WgnAaH_9keccak2568keccak_f:
.Lfunc_begin79:
	.cfi_startproc
	sub	sp, sp, #192
	.cfi_def_cfa_offset 192
	stp	x28, x27, [sp, #112]
	stp	x26, x25, [sp, #128]
	stp	x24, x23, [sp, #144]
	stp	x22, x21, [sp, #160]
	stp	x20, x19, [sp, #176]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -96
	ldp	x15, x8, [x0, #32]
	mov	x27, xzr
	ldp	x5, x12, [x0, #112]
	str	x0, [sp, #8]
	ldp	x9, x10, [x0]
	ldp	x11, x2, [x0, #80]
	mov	x22, x15
	ldp	x4, x13, [x0, #48]
	str	x8, [sp, #80]
	eor	x8, x8, x9
	str	x12, [sp, #40]
	ldp	x19, x3, [x0, #128]
	stp	x11, x9, [sp, #48]
	eor	x9, x11, x12
	stp	x30, x10, [sp, #96]
	ldp	x11, x14, [x0, #16]
	eor	x8, x8, x9
	ldp	x1, x7, [x0, #96]
	eor	x9, x4, x10
	ldp	x25, x21, [x0, #144]
	eor	x10, x2, x19
	ldp	x12, x6, [x0, #64]
	eor	x9, x9, x10
	str	x11, [sp, #88]
	eor	x10, x13, x11
	eor	x11, x1, x3
	stp	x14, x13, [sp, #64]
	eor	x10, x10, x11
	eor	x13, x7, x25
	eor	x11, x12, x14
	ldp	x23, x18, [x0, #160]
	ldp	x16, x20, [x0, #176]
	eor	x11, x11, x13
	eor	x13, x6, x15
	eor	x14, x5, x21
	eor	x13, x13, x14
	ldr	x14, [x0, #192]
	eor	x28, x8, x23
	eor	x30, x9, x18
	eor	x8, x10, x16
	eor	x15, x11, x20
	eor	x0, x13, x14
.LBB79_1:
	str	x5, [sp, #32]
	mov	x24, x2
	eor	x2, x0, x30, ror #63
	mov	x26, x3
	eor	x3, x30, x15, ror #63
	eor	x30, x28, x8, ror #63
	eor	x5, x8, x0, ror #63
	ldr	x8, [sp, #56]
	stp	x12, x18, [sp, #16]
	eor	x15, x15, x28, ror #63
	eor	x9, x1, x3
	ldr	x13, [sp, #104]
	eor	x12, x8, x2
	eor	x8, x4, x30
	eor	x10, x25, x5
	ror	x4, x8, #20
	ror	x1, x10, #43
	ldr	x8, [sp, #64]
	ldr	x10, [sp, #48]
	eor	x11, x14, x15
	ror	x17, x9, #21
	eor	x9, x6, x15
	ror	x18, x11, #50
	eor	x8, x8, x5
	eor	x11, x10, x2
	ror	x10, x9, #44
	eor	x9, x16, x3
	ror	x6, x8, #36
	eor	x8, x19, x30
	eor	x16, x13, x30
	ror	x14, x9, #3
	eor	x9, x7, x5
	ror	x13, x8, #19
	ror	x19, x16, #63
	ldr	x8, [sp, #72]
	ror	x16, x9, #39
	ldp	x9, x7, [sp, #80]
	eor	x0, x21, x15
	eor	x8, x8, x3
	ror	x21, x0, #56
	eor	x0, x22, x15
	ror	x25, x8, #58
	eor	x8, x23, x2
	eor	x23, x26, x3
	eor	x3, x7, x3
	ldr	x7, [sp, #16]
	eor	x22, x9, x2
	ror	x9, x8, #46
	ror	x8, x0, #37
	ror	x0, x22, #28
	eor	x22, x24, x30
	eor	x24, x20, x5
	eor	x5, x7, x5
	ldr	x7, [sp, #32]
	ror	x26, x22, #54
	ror	x22, x23, #49
	ror	x23, x24, #8
	ror	x3, x3, #2
	ror	x24, x5, #9
	eor	x15, x7, x15
	bic	x5, x1, x17
	ror	x11, x11, #61
	ror	x20, x15, #25
	ldr	x15, [sp, #40]
	eor	x7, x5, x4
	adrp	x5, .Lanon.47fac95803119c4a094797088418c9d4.1
	add	x5, x5, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.1
	str	x3, [sp, #32]
	eor	x2, x15, x2
	ldr	x15, [sp, #24]
	ldr	x5, [x5, x27]
	ror	x28, x2, #23
	bic	x2, x18, x1
	str	x7, [sp, #104]
	eor	x3, x15, x30
	eor	x2, x2, x17
	bic	x17, x17, x4
	ror	x30, x3, #62
	bic	x3, x12, x18
	add	x27, x27, #8
	eor	x3, x3, x1
	bic	x1, x4, x12
	eor	x12, x5, x12
	eor	x15, x18, x1
	eor	x5, x17, x12
	bic	x17, x11, x10
	bic	x18, x13, x11
	eor	x1, x17, x6
	bic	x17, x14, x13
	eor	x4, x18, x10
	bic	x10, x10, x6
	eor	x17, x17, x11
	bic	x11, x6, x14
	eor	x6, x14, x10
	bic	x14, x19, x9
	eor	x12, x11, x13
	eor	x11, x7, x4
	eor	x7, x14, x21
	bic	x14, x21, x16
	stp	x1, x2, [sp, #80]
	eor	x13, x2, x17
	eor	x2, x14, x25
	bic	x14, x25, x19
	stp	x5, x3, [sp, #56]
	eor	x10, x5, x1
	bic	x18, x9, x21
	eor	x5, x9, x14
	bic	x9, x26, x0
	eor	x1, x18, x16
	bic	x16, x16, x25
	eor	x18, x9, x8
	bic	x9, x22, x26
	eor	x16, x16, x19
	bic	x14, x23, x22
	eor	x19, x9, x0
	bic	x9, x0, x8
	bic	x8, x8, x23
	str	x17, [sp, #72]
	eor	x17, x3, x12
	eor	x3, x14, x26
	eor	x25, x8, x22
	eor	x8, x16, x18
	eor	x21, x23, x9
	eor	x8, x10, x8
	eor	x10, x1, x3
	eor	x10, x13, x10
	mov	x22, x15
	eor	x13, x15, x6
	eor	x14, x5, x21
	ldr	x15, [sp, #32]
	eor	x9, x2, x19
	eor	x13, x13, x14
	bic	x14, x20, x24
	eor	x9, x11, x9
	eor	x11, x7, x25
	eor	x23, x14, x15
	bic	x14, x28, x20
	stp	x18, x16, [sp, #40]
	eor	x11, x17, x11
	bic	x17, x30, x28
	eor	x18, x14, x24
	bic	x14, x24, x15
	bic	x15, x15, x30
	eor	x16, x17, x20
	eor	x20, x15, x28
	eor	x14, x30, x14
	eor	x28, x8, x23
	eor	x30, x9, x18
	cmp	x27, #192
	eor	x8, x10, x16
	eor	x15, x11, x20
	eor	x0, x13, x14
	b.ne	.LBB79_1
	ldr	x8, [sp, #8]
	ldr	x10, [sp, #56]
	ldp	x30, x9, [sp, #96]
	ldp	x28, x27, [sp, #112]
	stp	x10, x9, [x8]
	ldr	x10, [sp, #88]
	ldr	x9, [sp, #64]
	stp	x19, x3, [x8, #128]
	stp	x10, x9, [x8, #16]
	ldp	x9, x10, [sp, #72]
	stp	x25, x21, [x8, #144]
	ldp	x26, x25, [sp, #128]
	stp	x23, x18, [x8, #160]
	ldp	x24, x23, [sp, #144]
	stp	x22, x10, [x8, #32]
	ldp	x22, x21, [sp, #160]
	stp	x4, x9, [x8, #48]
	ldp	x9, x10, [sp, #40]
	stp	x16, x20, [x8, #176]
	ldp	x20, x19, [sp, #176]
	stp	x12, x6, [x8, #64]
	stp	x10, x2, [x8, #80]
	stp	x1, x7, [x8, #96]
	stp	x5, x9, [x8, #112]
	str	x14, [x8, #192]
	add	sp, sp, #192
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	ret
.Lfunc_end79:
	.size	_RNvCsndc0WgnAaH_9keccak2568keccak_f, .Lfunc_end79-_RNvCsndc0WgnAaH_9keccak2568keccak_f
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,"ax",@progbits
	.p2align	2
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update:
.Lfunc_begin80:
	.cfi_startproc
	stp	x29, x30, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	mov	x29, sp
	.cfi_def_cfa w29, 64
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -56
	.cfi_offset w29, -64
	.cfi_remember_state
	mov	x20, x0
	ldr	x0, [x0, #336]
	mov	x19, x2
	mov	x21, x1
	add	x23, x20, #200
	mov	w24, #136
	b	.LBB80_2
.LBB80_1:
	sub	x19, x19, x22
	add	x21, x21, x22
	cbz	x19, .LBB80_6
.LBB80_2:
	sub	x8, x24, x0
	cmp	x19, x8
	csel	x22, x19, x8, lo
	add	x1, x22, x0
	cmp	x1, x0
	b.lo	.LBB80_7
	cmp	x1, #137
	b.hs	.LBB80_7
	add	x0, x23, x0
	mov	x1, x21
	mov	x2, x22
	bl	memcpy
	ldr	x8, [x20, #336]
	add	x0, x8, x22
	cmp	x0, #136
	str	x0, [x20, #336]
	b.ne	.LBB80_1
	ldp	x8, x9, [x20, #200]
	ldr	x1, [x20, #280]
	ldp	x16, x0, [x20]
	ldp	x10, x11, [x20, #216]
	ldp	x12, x13, [x20, #232]
	eor	x8, x16, x8
	eor	x9, x0, x9
	ldp	x16, x0, [x20, #16]
	stp	x8, x9, [x20]
	ldp	x14, x15, [x20, #248]
	ldp	x17, x18, [x20, #264]
	eor	x8, x16, x10
	eor	x10, x0, x11
	mov	x0, x20
	ldp	x9, x11, [x20, #32]
	stp	x8, x10, [x20, #16]
	eor	x8, x9, x12
	eor	x10, x11, x13
	ldp	x9, x11, [x20, #48]
	stp	x8, x10, [x20, #32]
	ldp	x13, x10, [x20, #80]
	eor	x8, x9, x14
	ldp	x12, x9, [x20, #64]
	eor	x11, x11, x15
	eor	x13, x13, x1
	stp	x8, x11, [x20, #48]
	ldp	x14, x8, [x20, #288]
	eor	x12, x12, x17
	eor	x9, x9, x18
	stp	x12, x9, [x20, #64]
	ldp	x11, x12, [x20, #96]
	eor	x10, x10, x14
	ldp	x14, x9, [x20, #304]
	stp	x13, x10, [x20, #80]
	eor	x8, x11, x8
	ldp	x11, x10, [x20, #112]
	eor	x12, x12, x14
	stp	x8, x12, [x20, #96]
	ldp	x13, x8, [x20, #320]
	eor	x9, x11, x9
	ldr	x11, [x20, #128]
	eor	x10, x10, x13
	eor	x8, x11, x8
	stp	x9, x10, [x20, #112]
	str	x8, [x20, #128]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [x20, #336]
	b	.LBB80_1
.LBB80_6:
	mov	x0, x20
	.cfi_def_cfa wsp, 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldp	x29, x30, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB80_7:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.Lfunc_end80:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update, .Lfunc_end80-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,"ax",@progbits
	.p2align	2
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize:
.Lfunc_begin81:
	.cfi_startproc
	sub	sp, sp, #384
	.cfi_def_cfa_offset 384
	stp	x29, x30, [sp, #336]
	stp	x28, x21, [sp, #352]
	stp	x20, x19, [sp, #368]
	add	x29, sp, #336
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w28, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	.cfi_remember_state
	mov	x19, x0
	mov	x0, sp
	mov	w2, #200
	mov	x21, x1
	bl	memcpy
	ldr	x20, [x21, #336]
	cmp	x20, #137
	b.hs	.LBB81_3
	cmp	x20, #136
	b.eq	.LBB81_4
	sub	x0, x29, #136
	add	x1, x21, #200
	mov	x2, x20
	stp	xzr, xzr, [x29, #-16]
	sub	x21, x29, #136
	stp	xzr, xzr, [x29, #-32]
	stp	xzr, xzr, [x29, #-48]
	stp	xzr, xzr, [x29, #-64]
	stp	xzr, xzr, [x29, #-80]
	stp	xzr, xzr, [x29, #-96]
	stp	xzr, xzr, [x29, #-112]
	stp	xzr, xzr, [x29, #-128]
	stur	xzr, [x29, #-136]
	bl	memcpy
	ldrb	w8, [x21, x20]
	eor	w8, w8, #0x1
	strb	w8, [x21, x20]
	ldp	x8, x0, [sp]
	ldurb	w9, [x29, #-1]
	ldp	x10, x11, [x29, #-136]
	ldur	x1, [x29, #-56]
	ldp	x12, x13, [x29, #-120]
	eor	w9, w9, #0x80
	ldp	x14, x15, [x29, #-104]
	sturb	w9, [x29, #-1]
	eor	x8, x8, x10
	eor	x11, x0, x11
	ldp	x10, x0, [sp, #16]
	stp	x8, x11, [sp]
	ldp	x16, x17, [x29, #-88]
	ldp	x9, x18, [x29, #-72]
	eor	x8, x10, x12
	ldp	x10, x12, [sp, #32]
	eor	x11, x0, x13
	mov	x0, sp
	stp	x8, x11, [sp, #16]
	eor	x8, x10, x14
	eor	x11, x12, x15
	ldp	x10, x12, [sp, #48]
	stp	x8, x11, [sp, #32]
	eor	x8, x10, x16
	ldp	x13, x10, [sp, #64]
	eor	x12, x12, x17
	stp	x8, x12, [sp, #48]
	ldp	x14, x8, [x29, #-48]
	eor	x9, x13, x9
	ldp	x13, x11, [sp, #80]
	eor	x10, x10, x18
	stp	x9, x10, [sp, #64]
	ldp	x12, x9, [sp, #96]
	eor	x11, x11, x14
	ldp	x14, x10, [x29, #-32]
	eor	x13, x13, x1
	eor	x8, x12, x8
	stp	x13, x11, [sp, #80]
	eor	x9, x9, x14
	ldp	x12, x11, [sp, #112]
	stp	x8, x9, [sp, #96]
	ldp	x13, x8, [x29, #-16]
	ldr	x9, [sp, #128]
	eor	x10, x12, x10
	eor	x11, x11, x13
	eor	x8, x9, x8
	stp	x10, x11, [sp, #112]
	str	x8, [sp, #128]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldp	x8, x9, [sp]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #16]
	stp	x8, x10, [x19, #16]
	.cfi_def_cfa wsp, 384
	ldp	x20, x19, [sp, #368]
	ldp	x28, x21, [sp, #352]
	ldp	x29, x30, [sp, #336]
	add	sp, sp, #384
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB81_3:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x20
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB81_4:
	adrp	x0, .Lanon.47fac95803119c4a094797088418c9d4.8
	add	x0, x0, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.8
	adrp	x2, .Lanon.47fac95803119c4a094797088418c9d4.9
	add	x2, x2, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.9
	mov	w1, #99
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.Lfunc_end81:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize, .Lfunc_end81-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	.cfi_endproc

	.section	.text._RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,"ax",@progbits
	.p2align	2
	.type	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,@function
_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read:
.Lfunc_begin82:
	.cfi_startproc
	stp	x29, x30, [sp, #-80]!
	.cfi_def_cfa_offset 80
	str	x28, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	mov	x29, sp
	.cfi_def_cfa w29, 80
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w28, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	.cfi_remember_state
	sub	sp, sp, #1856
	ldr	xzr, [sp]
	ldr	x22, [x1, #8]
	cmp	x22, #15
	b.ls	.LBB82_21
	sub	x8, x22, #16
	ldr	x21, [x1]
	mov	x20, x1
	lsr	x8, x8, #4
	mov	x19, x0
	mov	x23, xzr
	add	x9, sp, #928
.LBB82_2:
	cbz	x8, .LBB82_21
	add	x10, x21, x23
	add	x12, x9, x23
	add	x23, x23, #16
	add	x11, x10, #32
	ldp	x13, x10, [x10, #16]
	sub	x24, x22, #32
	cmp	x23, #928
	sub	x8, x8, #1
	sub	x22, x22, #16
	stp	x11, x24, [x20]
	stp	x13, x10, [x12]
	b.ne	.LBB82_2
	mov	x0, sp
	add	x1, sp, #928
	mov	w2, #928
	bl	memcpy
	cmp	x24, #15
	b.ls	.LBB82_21
	add	x8, x21, x23
	and	x9, x24, #0xfffffffffffffff0
	ldp	x10, x11, [x8, #16]
	cmp	x9, #16
	str	x10, [sp, #928]
	str	x11, [sp, #936]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #32]
	cmp	x9, #32
	str	x10, [sp, #944]
	str	x11, [sp, #952]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #48]
	cmp	x9, #48
	str	x10, [sp, #960]
	str	x11, [sp, #968]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #64]
	cmp	x9, #64
	str	x10, [sp, #976]
	str	x11, [sp, #984]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #80]
	cmp	x9, #80
	str	x10, [sp, #992]
	str	x11, [sp, #1000]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #96]
	cmp	x9, #96
	str	x10, [sp, #1008]
	str	x11, [sp, #1016]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #112]
	cmp	x9, #112
	str	x10, [sp, #1024]
	str	x11, [sp, #1032]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #128]
	and	x12, x22, #0xfffffffffffffff0
	cmp	x12, #144
	str	x10, [sp, #1040]
	str	x11, [sp, #1048]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #144]
	cmp	x9, #144
	str	x10, [sp, #1056]
	str	x11, [sp, #1064]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #160]
	cmp	x9, #160
	str	x10, [sp, #1072]
	str	x11, [sp, #1080]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #176]
	cmp	x9, #176
	str	x10, [sp, #1088]
	str	x11, [sp, #1096]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #192]
	cmp	x9, #192
	str	x10, [sp, #1104]
	str	x11, [sp, #1112]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #208]
	cmp	x9, #208
	str	x10, [sp, #1120]
	str	x11, [sp, #1128]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #224]
	cmp	x9, #224
	str	x10, [sp, #1136]
	str	x11, [sp, #1144]
	b.eq	.LBB82_21
	ldp	x10, x11, [x8, #240]
	cmp	x9, #240
	str	x10, [sp, #1152]
	str	x11, [sp, #1160]
	b.eq	.LBB82_21
	add	x9, x8, #272
	sub	x10, x22, #272
	add	x1, sp, #928
	stp	x9, x10, [x20]
	ldp	x9, x8, [x8, #256]
	mov	x0, x19
	mov	w2, #256
	str	x9, [sp, #1168]
	str	x8, [sp, #1176]
	bl	memcpy
	ldp	x8, x9, [x21]
	add	x0, x19, #256
	mov	x1, sp
	mov	w2, #928
	str	x8, [x19, #1184]
	str	x9, [x19, #1192]
	bl	memcpy
	add	sp, sp, #1856
	.cfi_def_cfa wsp, 80
	ldp	x20, x19, [sp, #64]
	ldr	x28, [sp, #16]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x29, x30, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB82_21:
	.cfi_restore_state
	adrp	x0, .Lanon.e3df3b3b29d21204f5358235f5c92520.2
	add	x0, x0, :lo12:.Lanon.e3df3b3b29d21204f5358235f5c92520.2
	bl	_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed
.Lfunc_end82:
	.size	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read, .Lfunc_end82-_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	.cfi_endproc

	.section	.text._RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,"ax",@progbits
	.p2align	2
	.type	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,@function
_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf:
.Lfunc_begin83:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	mov	x29, sp
	.cfi_def_cfa w29, 96
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	sub	sp, sp, #2656
	lsl	w8, w2, #7
	lsl	w9, w2, #23
	ldr	xzr, [sp]
	mov	x20, x1
	mov	x19, x0
	add	x0, sp, #32
	strb	w8, [sp, #1782]
	mov	w8, #12
	mov	w1, wzr
	mov	w2, #344
	mov	x22, x7
	mov	x23, x6
	mov	x24, x5
	mov	x25, x4
	stp	w3, w9, [sp, #24]
	str	w3, [sp, #1776]
	strh	w9, [sp, #1780]
	strb	w8, [sp, #1783]
	str	xzr, [sp, #1784]
	bl	memset
	add	x0, sp, #32
	mov	x1, x20
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	add	x1, sp, #1776
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	mov	x1, x25
	mov	x2, x24
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	mov	x1, x23
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1776
	add	x1, sp, #32
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #1784]
	tst	x8, #0xfff0000000000000
	b.ne	.LBB83_5
	mov	x10, #6148914691236517205
	ldr	x9, [sp, #1776]
	mov	x11, #-6148914691236517206
	movk	x10, #5, lsl #48
	movk	x11, #10, lsl #48
	and	x10, x8, x10
	lsr	x13, x9, #2
	and	x14, x9, #0xaaaaaaaaaaaaaaaa
	lsr	x12, x10, #2
	sub	x14, x14, x14, lsr #1
	and	x11, x8, x11
	and	x10, x10, #0x3333333333333333
	and	x15, x9, #0x1111111111111111
	and	x13, x13, #0x1111111111111111
	and	x12, x12, #0x3333333333333333
	sub	x11, x11, x11, lsr #1
	add	x10, x10, x12
	add	x12, x15, x13
	lsr	x13, x14, #2
	lsr	x16, x11, #2
	and	x14, x14, #0x3333333333333333
	add	x12, x12, x12, lsr #4
	and	x13, x13, #0x3333333333333333
	and	x11, x11, #0x3333333333333333
	add	x10, x10, x10, lsr #4
	add	x13, x14, x13
	and	x14, x16, #0x3333333333333333
	mov	x15, #72340172838076673
	add	x13, x13, x13, lsr #4
	add	x11, x11, x14
	and	x12, x12, #0xf0f0f0f0f0f0f0f
	add	x11, x11, x11, lsr #4
	mul	x12, x12, x15
	and	x10, x10, #0xf0f0f0f0f0f0f0f
	and	x13, x13, #0xf0f0f0f0f0f0f0f
	mul	x13, x13, x15
	and	x11, x11, #0xf0f0f0f0f0f0f0f
	mul	x10, x10, x15
	lsr	x12, x12, #56
	mul	x11, x11, x15
	lsr	x13, x13, #56
	add	x10, x12, x10, lsr #56
	add	x11, x13, x11, lsr #56
	add	w10, w10, w11, lsl #1
	cmp	w10, #106
	b.ne	.LBB83_5
	add	x11, sp, #380
	lsl	x10, x8, #1
	mov	w12, #6
	orr	x11, x11, #0x1
	str	x19, [sp]
.LBB83_3:
	sub	x13, x12, #6
	sub	x14, x12, #4
	sub	x15, x12, #2
	mvn	w17, w13
	mvn	w1, w14
	lsr	x16, x9, x13
	lsr	x0, x9, x14
	lsl	x17, x10, x17
	lsl	x1, x10, x1
	lsr	x18, x8, x13
	mvn	w2, w15
	tst	x13, #0x40
	orr	x16, x17, x16
	orr	x17, x1, x0
	lsr	x0, x8, x14
	lsr	x13, x9, x15
	lsl	x2, x10, x2
	csel	x16, x18, x16, ne
	tst	x14, #0x40
	mvn	w18, w12
	and	w16, w16, #0x3
	csel	x14, x0, x17, ne
	lsr	x17, x8, x15
	orr	x13, x2, x13
	tst	x15, #0x40
	lsr	x15, x9, x12
	lsl	x18, x10, x18
	csel	x13, x17, x13, ne
	lsr	x17, x8, x12
	tst	x12, #0x40
	orr	x15, x18, x15
	and	w14, w14, #0x3
	and	w13, w13, #0x3
	csel	x15, x17, x15, ne
	strb	w14, [x11]
	add	x12, x12, #8
	and	w14, w15, #0x3
	sturb	w16, [x11, #-1]
	cmp	x12, #118
	strb	w13, [x11, #1]
	strb	w14, [x11, #2]
	add	x11, x11, #4
	b.ne	.LBB83_3
	ubfx	x9, x8, #48, #2
	lsr	x8, x8, #50
	add	x10, sp, #1776
	add	x11, sp, #1432
	mov	x28, xzr
	add	x21, x10, #200
	strb	w8, [sp, #437]
	ldr	w8, [sp, #28]
	add	x23, x11, #200
	strb	w9, [sp, #436]
	add	x9, sp, #380
	mov	w19, #136
	lsr	w8, w8, #16
	str	x22, [sp, #8]
	str	w8, [sp, #20]
	b	.LBB83_8
.LBB83_5:
	strb	wzr, [x19]
.LBB83_6:
	add	sp, sp, #2656
	.cfi_def_cfa wsp, 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB83_7:
	.cfi_restore_state
	add	x8, sp, #440
	ldr	x9, [sp, #1384]
	ldr	x10, [sp, #1392]
	add	x8, x8, x28, lsl #4
	add	x28, x28, #1
	ldr	x22, [sp, #8]
	cmp	x28, #58
	stp	x9, x10, [x8]
	add	x9, sp, #380
	b.eq	.LBB83_27
.LBB83_8:
	add	x8, x22, x28, lsl #4
	ldrb	w22, [x9, x28]
	ldp	x9, x8, [x8]
	cmp	x22, #2
	str	x9, [sp, #1384]
	str	x8, [sp, #1392]
	b.hi	.LBB83_7
.LBB83_9:
	ldr	x8, [sp, #1384]
	ldr	x9, [sp, #1392]
	add	x0, sp, #1776
	mov	w1, wzr
	mov	w2, #344
	str	xzr, [sp, #1424]
	str	x8, [sp, #1400]
	str	x9, [sp, #1408]
	ldp	w9, w8, [sp, #20]
	str	x28, [sp, #1416]
	stur	xzr, [x29, #-144]
	stur	w8, [x29, #-152]
	mov	w8, #1
	orr	w8, w8, w22, lsl #5
	sturb	w9, [x29, #-146]
	ldr	w9, [sp, #28]
	sturh	w9, [x29, #-148]
	sturb	w8, [x29, #-145]
	bl	memset
	ldr	x8, [sp, #2112]
	ldp	x9, x10, [x20]
	add	x0, x8, #16
	cmp	x0, #136
	stp	x9, x10, [x21]
	str	x0, [sp, #2112]
	b.ne	.LBB83_11
	ldr	x9, [sp, #1976]
	ldr	x14, [sp, #1776]
	ldr	x10, [sp, #1984]
	ldr	x15, [sp, #1784]
	ldr	x8, [sp, #1992]
	ldr	x16, [sp, #2000]
	eor	x9, x14, x9
	ldr	x14, [sp, #1800]
	ldr	x12, [sp, #2008]
	eor	x10, x15, x10
	str	x9, [sp, #1776]
	ldr	x9, [sp, #1792]
	str	x10, [sp, #1784]
	ldr	x10, [sp, #1808]
	ldr	x13, [sp, #2016]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #2024]
	str	x8, [sp, #1792]
	ldr	x8, [sp, #1816]
	ldr	x15, [sp, #2032]
	str	x9, [sp, #1800]
	eor	x9, x10, x12
	ldr	x10, [sp, #1824]
	eor	x8, x8, x13
	ldr	x18, [sp, #2040]
	ldr	x12, [sp, #1832]
	ldr	x13, [sp, #1840]
	ldr	x14, [sp, #2048]
	ldr	x0, [sp, #1848]
	str	x8, [sp, #1816]
	eor	x8, x10, x11
	ldr	x16, [sp, #2056]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1776
	str	x9, [sp, #1808]
	eor	x9, x12, x15
	ldr	x13, [sp, #2064]
	str	x8, [sp, #1824]
	ldr	x8, [sp, #1864]
	ldr	x12, [sp, #1856]
	ldr	x14, [sp, #2072]
	str	x9, [sp, #1832]
	ldr	x9, [sp, #1872]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1840]
	eor	x9, x9, x14
	ldr	x10, [sp, #2080]
	str	x11, [sp, #1848]
	ldr	x11, [sp, #1880]
	ldr	x13, [sp, #2088]
	str	x8, [sp, #1864]
	ldr	x8, [sp, #1888]
	ldr	x17, [sp, #1904]
	str	x12, [sp, #1856]
	eor	x10, x11, x10
	ldr	x11, [sp, #2096]
	str	x9, [sp, #1872]
	eor	x8, x8, x13
	ldr	x9, [sp, #1896]
	ldr	x12, [sp, #2104]
	str	x8, [sp, #1888]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1880]
	str	x9, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #2112]
.LBB83_11:
	add	x22, x22, #1
	sub	x24, x29, #152
	mov	w26, #16
	b	.LBB83_13
.LBB83_12:
	sub	x26, x26, x25
	add	x24, x24, x25
	cbz	x26, .LBB83_17
.LBB83_13:
	sub	x8, x19, x0
	cmp	x26, x8
	csel	x25, x26, x8, lo
	add	x1, x25, x0
	cmp	x1, x0
	b.lo	.LBB83_25
	cmp	x1, #137
	b.hs	.LBB83_25
	add	x0, x21, x0
	mov	x1, x24
	mov	x2, x25
	bl	memcpy
	ldr	x8, [sp, #2112]
	add	x0, x8, x25
	cmp	x0, #136
	str	x0, [sp, #2112]
	b.ne	.LBB83_12
	ldr	x9, [sp, #1976]
	ldr	x14, [sp, #1776]
	ldr	x10, [sp, #1984]
	ldr	x15, [sp, #1784]
	ldr	x8, [sp, #1992]
	ldr	x16, [sp, #2000]
	eor	x9, x14, x9
	ldr	x14, [sp, #1800]
	ldr	x12, [sp, #2008]
	eor	x10, x15, x10
	str	x9, [sp, #1776]
	ldr	x9, [sp, #1792]
	str	x10, [sp, #1784]
	ldr	x10, [sp, #1808]
	ldr	x13, [sp, #2016]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #2024]
	str	x8, [sp, #1792]
	ldr	x8, [sp, #1816]
	ldr	x15, [sp, #2032]
	str	x9, [sp, #1800]
	eor	x9, x10, x12
	ldr	x10, [sp, #1824]
	eor	x8, x8, x13
	ldr	x18, [sp, #2040]
	ldr	x12, [sp, #1832]
	ldr	x13, [sp, #1840]
	ldr	x14, [sp, #2048]
	ldr	x0, [sp, #1848]
	str	x8, [sp, #1816]
	eor	x8, x10, x11
	ldr	x16, [sp, #2056]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1776
	str	x9, [sp, #1808]
	eor	x9, x12, x15
	ldr	x13, [sp, #2064]
	str	x8, [sp, #1824]
	ldr	x8, [sp, #1864]
	ldr	x12, [sp, #1856]
	ldr	x14, [sp, #2072]
	str	x9, [sp, #1832]
	ldr	x9, [sp, #1872]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1840]
	eor	x9, x9, x14
	ldr	x10, [sp, #2080]
	str	x11, [sp, #1848]
	ldr	x11, [sp, #1880]
	ldr	x13, [sp, #2088]
	str	x8, [sp, #1864]
	ldr	x8, [sp, #1888]
	ldr	x17, [sp, #1904]
	str	x12, [sp, #1856]
	eor	x10, x11, x10
	ldr	x11, [sp, #2096]
	str	x9, [sp, #1872]
	eor	x8, x8, x13
	ldr	x9, [sp, #1896]
	ldr	x12, [sp, #2104]
	str	x8, [sp, #1888]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1880]
	str	x9, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #2112]
	b	.LBB83_12
.LBB83_17:
	add	x0, sp, #1432
	add	x1, sp, #1776
	mov	w2, #344
	bl	memcpy
	ldr	x26, [sp, #1768]
	add	x24, sp, #1400
	mov	w27, #32
	b	.LBB83_19
.LBB83_18:
	sub	x27, x27, x25
	add	x24, x24, x25
	cbz	x27, .LBB83_23
.LBB83_19:
	sub	x8, x19, x26
	cmp	x27, x8
	csel	x25, x27, x8, lo
	add	x1, x25, x26
	cmp	x1, x26
	b.lo	.LBB83_26
	cmp	x1, #137
	b.hs	.LBB83_26
	add	x0, x23, x26
	mov	x1, x24
	mov	x2, x25
	bl	memcpy
	ldr	x8, [sp, #1768]
	add	x26, x8, x25
	cmp	x26, #136
	str	x26, [sp, #1768]
	b.ne	.LBB83_18
	ldr	x9, [sp, #1632]
	ldr	x14, [sp, #1432]
	ldr	x10, [sp, #1640]
	ldr	x15, [sp, #1440]
	ldr	x8, [sp, #1648]
	ldr	x16, [sp, #1656]
	eor	x9, x14, x9
	ldr	x14, [sp, #1456]
	ldr	x12, [sp, #1664]
	eor	x10, x15, x10
	str	x9, [sp, #1432]
	ldr	x9, [sp, #1448]
	str	x10, [sp, #1440]
	ldr	x10, [sp, #1464]
	ldr	x13, [sp, #1672]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #1680]
	str	x8, [sp, #1448]
	ldr	x8, [sp, #1472]
	ldr	x15, [sp, #1688]
	str	x9, [sp, #1456]
	eor	x9, x10, x12
	ldr	x10, [sp, #1480]
	eor	x8, x8, x13
	ldr	x18, [sp, #1696]
	ldr	x12, [sp, #1488]
	ldr	x13, [sp, #1496]
	ldr	x14, [sp, #1704]
	ldr	x0, [sp, #1504]
	str	x8, [sp, #1472]
	eor	x8, x10, x11
	ldr	x16, [sp, #1712]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1432
	str	x9, [sp, #1464]
	eor	x9, x12, x15
	ldr	x13, [sp, #1720]
	str	x8, [sp, #1480]
	ldr	x8, [sp, #1520]
	ldr	x12, [sp, #1512]
	ldr	x14, [sp, #1728]
	str	x9, [sp, #1488]
	ldr	x9, [sp, #1528]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1496]
	eor	x9, x9, x14
	ldr	x10, [sp, #1736]
	str	x11, [sp, #1504]
	ldr	x11, [sp, #1536]
	ldr	x13, [sp, #1744]
	str	x8, [sp, #1520]
	ldr	x8, [sp, #1544]
	ldr	x17, [sp, #1560]
	str	x12, [sp, #1512]
	eor	x10, x11, x10
	ldr	x11, [sp, #1752]
	str	x9, [sp, #1528]
	eor	x8, x8, x13
	ldr	x9, [sp, #1552]
	ldr	x12, [sp, #1760]
	str	x8, [sp, #1544]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1536]
	str	x9, [sp, #1552]
	str	x8, [sp, #1560]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x26, xzr
	str	xzr, [sp, #1768]
	b	.LBB83_18
.LBB83_23:
	add	x0, sp, #1776
	add	x1, sp, #1432
	mov	w2, #200
	bl	memcpy
	cmp	x26, #137
	b.hs	.LBB83_28
	sub	x0, x29, #152
	mov	x1, x23
	mov	x2, x26
	stp	xzr, xzr, [x29, #-32]
	stp	xzr, xzr, [x29, #-48]
	stp	xzr, xzr, [x29, #-64]
	stp	xzr, xzr, [x29, #-80]
	stp	xzr, xzr, [x29, #-96]
	stp	xzr, xzr, [x29, #-112]
	stp	xzr, xzr, [x29, #-128]
	stp	xzr, xzr, [x29, #-144]
	stur	xzr, [x29, #-152]
	bl	memcpy
	sub	x9, x29, #152
	ldr	x0, [sp, #1784]
	ldrb	w8, [x9, x26]
	eor	w8, w8, #0x1
	strb	w8, [x9, x26]
	ldp	x10, x11, [x29, #-152]
	ldr	x8, [sp, #1776]
	ldp	x12, x13, [x29, #-136]
	ldurb	w9, [x29, #-17]
	ldp	x14, x15, [x29, #-120]
	ldur	x1, [x29, #-72]
	eor	x8, x8, x10
	ldr	x10, [sp, #1792]
	eor	x11, x0, x11
	str	x8, [sp, #1776]
	ldp	x16, x17, [x29, #-104]
	eor	x8, x10, x12
	ldr	x10, [sp, #1808]
	ldr	x0, [sp, #1800]
	str	x8, [sp, #1792]
	eor	w9, w9, #0x80
	ldr	x12, [sp, #1816]
	eor	x8, x10, x14
	ldr	x10, [sp, #1824]
	sturb	w9, [x29, #-17]
	ldp	x9, x18, [x29, #-88]
	str	x11, [sp, #1784]
	eor	x11, x0, x13
	str	x8, [sp, #1808]
	eor	x8, x10, x16
	str	x11, [sp, #1800]
	eor	x11, x12, x15
	ldr	x12, [sp, #1832]
	ldr	x10, [sp, #1848]
	str	x8, [sp, #1824]
	ldr	x13, [sp, #1840]
	ldp	x14, x8, [x29, #-64]
	str	x11, [sp, #1816]
	ldr	x11, [sp, #1864]
	eor	x12, x12, x17
	eor	x10, x10, x18
	eor	x9, x13, x9
	ldr	x13, [sp, #1856]
	str	x12, [sp, #1832]
	ldr	x12, [sp, #1872]
	eor	x11, x11, x14
	str	x10, [sp, #1848]
	ldp	x14, x10, [x29, #-48]
	str	x9, [sp, #1840]
	ldr	x9, [sp, #1880]
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x13, [sp, #1856]
	ldr	x12, [sp, #1888]
	add	x0, sp, #1776
	eor	x9, x9, x14
	str	x8, [sp, #1872]
	ldp	x13, x8, [x29, #-32]
	str	x11, [sp, #1864]
	ldr	x11, [sp, #1896]
	str	x9, [sp, #1880]
	ldr	x9, [sp, #1904]
	eor	x10, x12, x10
	eor	x11, x11, x13
	eor	x8, x9, x8
	str	x10, [sp, #1888]
	str	x11, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #1784]
	ldr	x9, [sp, #1776]
	cmp	x22, #3
	stp	x9, x8, [x29, #-152]
	str	x9, [sp, #1384]
	str	x8, [sp, #1392]
	b.ne	.LBB83_9
	b	.LBB83_7
.LBB83_25:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB83_26:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	x0, x26
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB83_27:
	ldp	w8, w9, [sp, #20]
	add	x0, sp, #2160
	mov	w1, wzr
	mov	w2, #344
	str	xzr, [sp, #1784]
	strb	w8, [sp, #1782]
	ldr	w8, [sp, #28]
	str	w9, [sp, #1776]
	strh	w8, [sp, #1780]
	mov	w8, #2
	strb	w8, [sp, #1783]
	bl	memset
	add	x0, sp, #2160
	mov	x1, x20
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2160
	add	x1, sp, #1776
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2160
	add	x1, sp, #440
	mov	w2, #928
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2128
	add	x1, sp, #2160
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	add	x11, sp, #380
	ldp	x8, x9, [x11, #32]
	ldr	x10, [x11, #48]
	str	x10, [sp, #1824]
	str	x8, [sp, #1808]
	ldrh	w8, [x11, #56]
	str	x9, [sp, #1816]
	strh	w8, [sp, #1832]
	ldp	x9, x8, [x11]
	str	x8, [sp, #1784]
	ldp	x10, x8, [x11, #16]
	str	x9, [sp, #1776]
	ldr	x9, [sp, #2136]
	add	x11, sp, #1776
	str	x10, [sp, #1792]
	ldr	x10, [sp, #2128]
	str	x8, [sp, #1800]
	ldr	x8, [sp, #1808]
	stur	x9, [x11, #66]
	ldr	x9, [sp, #1816]
	stur	x10, [x11, #58]
	ldr	x11, [sp]
	ldr	x10, [sp, #1832]
	stur	x8, [x11, #33]
	ldr	x8, [sp, #1824]
	stur	x9, [x11, #41]
	ldr	x9, [sp, #1776]
	stur	x8, [x11, #49]
	ldr	x8, [sp, #1784]
	stur	x9, [x11, #1]
	ldr	x9, [sp, #1792]
	stur	x8, [x11, #9]
	ldr	x8, [sp, #1800]
	stur	x9, [x11, #17]
	ldr	x9, [sp, #1840]
	stur	x8, [x11, #25]
	ldrh	w8, [sp, #1848]
	stur	x9, [x11, #65]
	sturh	w8, [x11, #73]
	mov	w8, #1
	stur	x10, [x11, #57]
	strb	w8, [x11]
	b	.LBB83_6
.LBB83_28:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x26
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.Lfunc_end83:
	.size	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf, .Lfunc_end83-_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	.cfi_endproc

	.type	.Lanon.47fac95803119c4a094797088418c9d4.1,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.1,"a",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.1:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.1, 192

	.type	.Lanon.47fac95803119c4a094797088418c9d4.3,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.47fac95803119c4a094797088418c9d4.3:
	.asciz	"crates/keccak256/src/lib.rs"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.3, 28

	.type	.Lanon.47fac95803119c4a094797088418c9d4.8,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.8,"a",@progbits
.Lanon.47fac95803119c4a094797088418c9d4.8:
	.ascii	"a final block holds fewer than RATE message bytes"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.8, 49

	.type	.Lanon.47fac95803119c4a094797088418c9d4.9,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.9,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.9:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000~\000\000\000\005\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.9, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.11,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.11,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.11:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000\245\000\000\000\025\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.11, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.12,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.12,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.12:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000\262\000\000\0002\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.12, 24

	.type	.Lanon.e3df3b3b29d21204f5358235f5c92520.1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.e3df3b3b29d21204f5358235f5c92520.1:
	.asciz	"crates/lean_xmss/src/scheme.rs"
	.size	.Lanon.e3df3b3b29d21204f5358235f5c92520.1, 31

	.type	.Lanon.e3df3b3b29d21204f5358235f5c92520.2,@object
	.section	.data.rel.ro..Lanon.e3df3b3b29d21204f5358235f5c92520.2,"aw",@progbits
	.p2align	3, 0x0
.Lanon.e3df3b3b29d21204f5358235f5c92520.2:
	.xword	.Lanon.e3df3b3b29d21204f5358235f5c92520.1
	.asciz	"\036\000\000\000\000\000\000\000G\000\000\0002\000\000"
	.size	.Lanon.e3df3b3b29d21204f5358235f5c92520.2, 24
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
