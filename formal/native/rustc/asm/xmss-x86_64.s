	.att_syntax
	.file	"xmss.e3b090c1caa48f6d-cgu.0"
	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	4
	.type	memcpy,@function
memcpy:
.Lfunc_begin0:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%esi, %ecx
	orl	%eax, %ecx
	movl	%edx, %edi
	orl	%ecx, %edi
	testb	$7, %dil
	je	.LBB0_4
	testq	%rdx, %rdx
	je	.LBB0_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB0_3:
	movzbl	(%rsi,%rcx), %edi
	movb	%dil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB0_3
	jmp	.LBB0_7
.LBB0_4:
	testq	%rdx, %rdx
	je	.LBB0_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB0_6:
	movq	(%rsi,%rcx), %rdi
	movq	%rdi, (%rax,%rcx)
	addq	$8, %rcx
	#APP
	#NO_APP
	cmpq	%rdx, %rcx
	jb	.LBB0_6
.LBB0_7:
	retq
.Lfunc_end0:
	.size	memcpy, .Lfunc_end0-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	4
	.type	memset,@function
memset:
.Lfunc_begin1:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%edx, %ecx
	orl	%eax, %ecx
	testb	$7, %cl
	je	.LBB1_4
	testq	%rdx, %rdx
	je	.LBB1_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB1_3:
	movb	%sil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB1_3
	jmp	.LBB1_7
.LBB1_4:
	testq	%rdx, %rdx
	je	.LBB1_7
	movzbl	%sil, %esi
	movabsq	$72340172838076673, %rcx
	imulq	%rsi, %rcx
	xorl	%esi, %esi
	.p2align	4
.LBB1_6:
	movq	%rcx, (%rax,%rsi)
	addq	$8, %rsi
	#APP
	#NO_APP
	cmpq	%rdx, %rsi
	jb	.LBB1_6
.LBB1_7:
	retq
.Lfunc_end1:
	.size	memset, .Lfunc_end1-memset
	.cfi_endproc

	.section	.text.xmss_verify,"ax",@progbits
	.globl	xmss_verify
	.p2align	4
	.type	xmss_verify,@function
xmss_verify:
.Lfunc_begin2:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$1640, %rsp
	.cfi_def_cfa_offset 5792
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, %r14
	leaq	932(%rsp), %rbx
	xorl	%r15d, %r15d
	movl	$2400, %edx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	1024(%r14), %rax
	movq	1032(%r14), %rcx
	movq	1040(%r14), %rdx
	movq	1048(%r14), %rsi
	movq	1056(%r14), %rdi
	movq	%rdi, 128(%rsp)
	movq	1064(%r14), %rdi
	movq	%rdi, 136(%rsp)
	movq	1072(%r14), %rdi
	movq	%rdi, 144(%rsp)
	movq	1080(%r14), %rdi
	movq	%rdi, 152(%rsp)
	movq	1088(%r14), %r13
	movl	%r13d, %ebp
	movl	%r13d, 928(%rsp)
	.p2align	4
.LBB2_1:
	movq	1096(%r14,%r15,8), %rdi
	movq	%rdi, 932(%rsp,%r15,8)
	movq	1104(%r14,%r15,8), %rdi
	movq	%rdi, 940(%rsp,%r15,8)
	movq	1112(%r14,%r15,8), %rdi
	movq	%rdi, 948(%rsp,%r15,8)
	movq	1120(%r14,%r15,8), %rdi
	movq	%rdi, 956(%rsp,%r15,8)
	movq	1128(%r14,%r15,8), %rdi
	movq	%rdi, 964(%rsp,%r15,8)
	movq	1136(%r14,%r15,8), %rdi
	movq	%rdi, 972(%rsp,%r15,8)
	addq	$6, %r15
	cmpq	$300, %r15
	jne	.LBB2_1
	leaq	32(%rsp), %r15
	movq	%rdx, 32(%rsp)
	movq	%rsi, 40(%rsp)
	movq	%rax, 16(%rsp)
	movq	%rcx, 24(%rsp)
	movq	%rbx, 160(%rsp)
	movq	$2400, 168(%rsp)
	leaq	3332(%rsp), %r12
	leaq	160(%rsp), %rbx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	callq	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	leaq	4532(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	movl	%r13d, 5732(%rsp)
	leaq	4516(%rsp), %rax
	leaq	3588(%rsp), %r10
	leaq	160(%rsp), %rdi
	leaq	128(%rsp), %r8
	movl	$32, %r9d
	movq	%r15, %rsi
	xorl	%edx, %edx
	movl	%r13d, %ecx
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpb	$1, 160(%rsp)
	jne	.LBB2_10
	movq	%r13, 56(%rsp)
	leaq	161(%rsp), %rsi
	leaq	510(%rsp), %rdi
	movl	$74, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	%rbp, %rbx
	xorl	%ebp, %ebp
	leaq	160(%rsp), %r15
	.p2align	4
.LBB2_4:
	leaq	568(%rsp), %r14
	movq	(%r14), %rax
	movq	8(%r14), %rcx
	movq	%rcx, 104(%rsp)
	movq	%rax, 96(%rsp)
	movl	$1, %eax
	movl	%ebp, %ecx
	shlq	%cl, %rax
	testl	%ebx, %eax
	movq	%r12, %rax
	leaq	96(%rsp), %rcx
	cmoveq	%rcx, %rax
	cmoveq	%r12, %rcx
	movq	(%rax), %rdx
	movq	8(%rax), %rax
	movq	%rax, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	80(%rsp), %rsi
	movq	%rcx, 8(%rsi)
	incq	%rbp
	movq	%rbx, %rdx
	movl	%ebp, %ecx
	shrq	%cl, %rdx
	movq	%rax, (%rsi)
	movl	%edx, (%rsp)
	movl	%ebp, %eax
	shrl	$16, %eax
	movb	%al, 6(%rsp)
	movw	%bp, 4(%rsp)
	movb	$3, 7(%rsp)
	movq	$0, 8(%rsp)
	movl	$344, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r15, %rdi
	leaq	32(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r15, %rdi
	movq	%rsp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	leaq	584(%rsp), %r13
	movq	%r13, %rdi
	movq	%r15, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movl	$32, %edx
	movq	%r13, %rdi
	leaq	64(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	160(%rsp), %rax
	movq	168(%rsp), %rcx
	movq	%rcx, 8(%r14)
	movq	%rax, (%r14)
	addq	$16, %r12
	cmpq	$16, %rbp
	jne	.LBB2_4
	movq	56(%rsp), %rbx
	shrl	$16, %ebx
	leaq	5716(%rsp), %rax
	leaq	4788(%rsp), %r10
	leaq	160(%rsp), %rdi
	movl	$1, %r12d
	movl	$1, %edx
	movl	$16, %r9d
	leaq	32(%rsp), %rsi
	leaq	568(%rsp), %r8
	movl	%ebx, %ecx
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpb	$1, 160(%rsp)
	jne	.LBB2_10
	movq	219(%rsp), %rcx
	movq	227(%rsp), %rdx
	movl	%ebx, %ebx
	leaq	160(%rsp), %r15
	leaq	584(%rsp), %rbp
	leaq	96(%rsp), %r13
	leaq	4532(%rsp), %r14
	.p2align	4
.LBB2_7:
	movq	%rcx, 96(%rsp)
	movq	%rdx, 104(%rsp)
	leal	-1(%r12), %ecx
	movl	$1, %eax
	shlq	%cl, %rax
	testl	%ebx, %eax
	movq	%r14, %rax
	cmoveq	%r13, %rax
	movq	%r13, %rcx
	cmoveq	%r14, %rcx
	movq	(%rax), %rdx
	movq	8(%rax), %rax
	movq	%rax, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	80(%rsp), %rdx
	movq	%rcx, 8(%rdx)
	movq	%rax, (%rdx)
	movq	%rbx, %rax
	movl	%r12d, %ecx
	shrq	%cl, %rax
	movl	%r12d, %ecx
	orl	$8388608, %ecx
	movl	%eax, (%rsp)
	shrl	$16, %ecx
	movb	%cl, 6(%rsp)
	movw	%r12w, 4(%rsp)
	movb	$3, 7(%rsp)
	movq	$0, 8(%rsp)
	movl	$344, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r15, %rdi
	leaq	32(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r15, %rdi
	movq	%rsp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r15, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movl	$32, %edx
	movq	%rbp, %rdi
	leaq	64(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rdx
	incq	%r12
	addq	$16, %r14
	cmpq	$17, %r12
	jne	.LBB2_7
	xorq	16(%rsp), %rcx
	xorq	24(%rsp), %rdx
	xorl	%eax, %eax
	orq	%rcx, %rdx
	sete	%al
	jmp	.LBB2_9
.LBB2_10:
	xorl	%eax, %eax
.LBB2_9:
	addq	$5736, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	xmss_verify, .Lfunc_end2-xmss_verify
	.cfi_endproc

	.section	.text._RNvCsndc0WgnAaH_9keccak2568keccak_f,"ax",@progbits
	.p2align	4
	.type	_RNvCsndc0WgnAaH_9keccak2568keccak_f,@function
_RNvCsndc0WgnAaH_9keccak2568keccak_f:
.Lfunc_begin81:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$112, %rsp
	.cfi_def_cfa_offset 168
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	(%rdi), %rdx
	movq	8(%rdi), %rsi
	movq	40(%rdi), %rax
	movq	80(%rdi), %r14
	movq	120(%rdi), %rcx
	movq	%rax, -88(%rsp)
	movq	%rdx, -40(%rsp)
	xorq	%rdx, %rax
	movq	%r14, -96(%rsp)
	movq	%rcx, 40(%rsp)
	xorq	%rcx, %r14
	xorq	%rax, %r14
	movq	48(%rdi), %rax
	movq	88(%rdi), %r9
	movq	128(%rdi), %rcx
	movq	%rax, -120(%rsp)
	movq	%rsi, 16(%rsp)
	xorq	%rsi, %rax
	movq	%r9, -72(%rsp)
	movq	%rcx, -48(%rsp)
	xorq	%rcx, %r9
	xorq	%rax, %r9
	movq	16(%rdi), %rcx
	movq	56(%rdi), %rax
	movq	96(%rdi), %rsi
	movq	%rax, -112(%rsp)
	movq	%rcx, 24(%rsp)
	xorq	%rcx, %rax
	movq	136(%rdi), %rcx
	movq	%rsi, %r13
	movq	%rcx, -56(%rsp)
	xorq	%rcx, %r13
	xorq	%rax, %r13
	movq	24(%rdi), %r11
	movq	64(%rdi), %rax
	movq	%rax, 32(%rsp)
	xorq	%r11, %rax
	movq	104(%rdi), %rbp
	movq	144(%rdi), %r8
	movq	%rbp, -64(%rsp)
	xorq	%r8, %rbp
	xorq	%rax, %rbp
	movq	32(%rdi), %rcx
	movq	72(%rdi), %rax
	movq	%rax, -80(%rsp)
	movq	%rcx, %r15
	xorq	%rcx, %rax
	movq	112(%rdi), %rcx
	movq	152(%rdi), %rdx
	movq	%rcx, -104(%rsp)
	movq	%rdx, -128(%rsp)
	xorq	%rdx, %rcx
	xorq	%rax, %rcx
	movq	160(%rdi), %r10
	xorq	%r10, %r14
	movq	168(%rdi), %rax
	movq	%rax, -16(%rsp)
	xorq	%rax, %r9
	movq	176(%rdi), %rax
	xorq	%rax, %r13
	movq	184(%rdi), %rdx
	movq	%rdx, -24(%rsp)
	xorq	%rdx, %rbp
	movq	%rdi, 88(%rsp)
	movq	192(%rdi), %rbx
	xorq	%rbx, %rcx
	movl	$8, %edi
	.p2align	4
.LBB81_1:
	movq	%rdi, 64(%rsp)
	movq	%rbp, %rdi
	rolq	%rdi
	xorq	%r9, %rdi
	movq	%rdi, %r12
	movq	%rdi, 48(%rsp)
	rolq	%r9
	xorq	%rcx, %r9
	movq	%r9, %rdx
	movq	%r13, %rdi
	rolq	%rdi
	xorq	%r14, %rdi
	movq	%rdi, -32(%rsp)
	rolq	%rcx
	rolq	%r14
	xorq	%r13, %rcx
	xorq	%rbp, %r14
	xorq	%r14, %rbx
	xorq	%r14, -80(%rsp)
	xorq	%r14, -128(%rsp)
	xorq	%r14, %r15
	movq	%r15, -8(%rsp)
	xorq	-104(%rsp), %r14
	xorq	%r12, %rsi
	rolq	$43, %rsi
	xorq	%rcx, %r8
	movq	-120(%rsp), %r13
	xorq	%rdi, %r13
	rolq	$21, %r8
	rolq	$44, %r13
	movq	-40(%rsp), %r9
	movq	%rdx, %r15
	xorq	%rdx, %r9
	rolq	$14, %rbx
	movq	%rsi, %rdi
	notq	%rdi
	andq	%r8, %rdi
	xorq	%r13, %rdi
	movq	%rdi, 80(%rsp)
	movq	%r9, %rbp
	notq	%rbp
	andq	%r13, %rbp
	notq	%r13
	andq	%rsi, %r13
	movq	%rbx, %r12
	notq	%r12
	andq	%r9, %r12
	xorq	%r8, %r12
	movq	%r12, 8(%rsp)
	notq	%r8
	andq	%rbx, %r8
	xorq	%rsi, %r8
	movq	%r8, 72(%rsp)
	xorq	%rbx, %rbp
	movq	%rbp, (%rsp)
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1(%rip), %rdx
	movq	64(%rsp), %rsi
	xorq	-8(%rsi,%rdx), %r13
	xorq	%r9, %r13
	movq	%r13, 104(%rsp)
	xorq	%rcx, %r11
	rolq	$28, %r11
	movq	-96(%rsp), %rbp
	xorq	%r15, %rbp
	rolq	$3, %rbp
	movq	-48(%rsp), %rdx
	movq	-32(%rsp), %r9
	xorq	%r9, %rdx
	rolq	$45, %rdx
	movq	-80(%rsp), %rsi
	rolq	$20, %rsi
	movq	48(%rsp), %r12
	xorq	%r12, %rax
	rolq	$61, %rax
	movq	%rsi, %r8
	movq	%rsi, %rbx
	movq	%rsi, -80(%rsp)
	notq	%r8
	movq	%rdx, %rsi
	notq	%rsi
	andq	%rbp, %r8
	andq	%rax, %rsi
	xorq	%rbp, %rsi
	movq	%rsi, -96(%rsp)
	notq	%rbp
	movq	%rax, %rsi
	notq	%rsi
	andq	%r11, %rsi
	andq	%rdx, %rbp
	movq	%rbp, 56(%rsp)
	xorq	%rdx, %rsi
	movq	%rsi, -104(%rsp)
	xorq	%r11, %r8
	movq	%r8, -48(%rsp)
	notq	%r11
	andq	%rbx, %r11
	movq	-112(%rsp), %rdx
	xorq	%r12, %rdx
	rolq	$6, %rdx
	xorq	%rax, %r11
	movq	%r11, -120(%rsp)
	movq	-64(%rsp), %r8
	xorq	%rcx, %r8
	rolq	$25, %r8
	movq	%r9, %rsi
	movq	16(%rsp), %rbx
	xorq	%r9, %rbx
	movq	%r15, 96(%rsp)
	xorq	%r15, %r10
	rolq	%rbx
	rolq	$18, %r10
	movq	-128(%rsp), %r13
	rolq	$8, %r13
	movq	%rdx, %rax
	notq	%rax
	andq	%r8, %rax
	xorq	%rbx, %rax
	movq	%rax, -64(%rsp)
	movq	%r13, %rax
	notq	%rax
	andq	%r10, %rax
	movq	%rax, -112(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	movq	%rax, -128(%rsp)
	notq	%rbx
	andq	%rdx, %rbx
	xorq	%r10, %rbx
	movq	%rbx, -40(%rsp)
	movq	-56(%rsp), %r9
	xorq	%r12, %r9
	movq	-88(%rsp), %rax
	xorq	%r15, %rax
	rolq	$15, %r9
	rolq	$36, %rax
	movq	-72(%rsp), %r10
	xorq	%rsi, %r10
	movq	-24(%rsp), %r11
	xorq	%rcx, %r11
	rolq	$10, %r10
	rolq	$56, %r11
	movq	-8(%rsp), %r15
	rolq	$27, %r15
	xorq	24(%rsp), %r12
	movq	%rax, %rsi
	notq	%rsi
	andq	%r10, %rsi
	movq	%r9, %rdi
	notq	%rdi
	andq	%r11, %rdi
	xorq	%r10, %rdi
	movq	%rdi, -24(%rsp)
	notq	%r10
	andq	%r9, %r10
	movq	%r11, %rbp
	notq	%rbp
	andq	%r15, %rbp
	xorq	%r9, %rbp
	movq	%rbp, -8(%rsp)
	xorq	%r15, %rsi
	movq	%rsi, -56(%rsp)
	xorq	%rax, %r10
	movq	%r10, -88(%rsp)
	notq	%r15
	andq	%rax, %r15
	xorq	%r11, %r15
	movq	%r15, %r9
	movq	%r15, -72(%rsp)
	movq	-112(%rsp), %r11
	xorq	%r8, %r11
	movq	%r11, -112(%rsp)
	movq	-96(%rsp), %rax
	xorq	72(%rsp), %rax
	xorq	%rdi, %r11
	xorq	%rax, %r11
	movq	56(%rsp), %rsi
	xorq	-80(%rsp), %rsi
	notq	%r8
	movq	-128(%rsp), %r15
	xorq	%r13, %r15
	movq	%r15, -128(%rsp)
	andq	%r13, %r8
	movq	%r8, %r13
	xorq	%rbp, %r15
	movq	-104(%rsp), %rax
	xorq	8(%rsp), %rax
	xorq	%rax, %r15
	movq	-120(%rsp), %rax
	xorq	(%rsp), %rax
	movq	%rbx, %r8
	xorq	%r9, %r8
	xorq	%rax, %r8
	xorq	32(%rsp), %rcx
	xorq	%rdx, %r13
	movq	%r13, 48(%rsp)
	movq	96(%rsp), %rax
	xorq	40(%rsp), %rax
	movq	-32(%rsp), %r9
	xorq	-16(%rsp), %r9
	rolq	$62, %r12
	rolq	$41, %rax
	rolq	$55, %rcx
	rolq	$2, %r9
	rolq	$39, %r14
	movq	%rcx, %r10
	notq	%r10
	andq	%r14, %r10
	movq	%rax, %rbp
	notq	%rbp
	andq	%r9, %rbp
	xorq	%r14, %rbp
	movq	%r14, %rbx
	notq	%rbx
	movq	%r9, %r14
	notq	%r14
	andq	%rax, %rbx
	andq	%r12, %r14
	xorq	%rax, %r14
	movq	%r14, -32(%rsp)
	xorq	%r12, %r10
	movq	%r10, 56(%rsp)
	xorq	%rcx, %rbx
	movq	%rbx, %rdi
	movq	%rbx, -16(%rsp)
	notq	%r12
	andq	%rcx, %r12
	xorq	%r9, %r12
	movq	%rsi, %rcx
	xorq	80(%rsp), %rcx
	xorq	-88(%rsp), %r13
	xorq	%rcx, %r13
	movq	-48(%rsp), %r9
	xorq	-64(%rsp), %r9
	xorq	-56(%rsp), %r9
	xorq	%r10, %r9
	movq	104(%rsp), %rdx
	xorq	%rdx, %r9
	xorq	%rbp, %r11
	xorq	%r14, %r15
	xorq	%r12, %r8
	movq	%r15, %rbx
	rolq	%rbx
	xorq	%rdi, %r13
	xorq	%r13, %rbx
	rolq	%r13
	xorq	%r8, %r13
	rolq	%r8
	xorq	%r11, %r8
	movq	%r11, %rdi
	rolq	%rdi
	xorq	%r9, %rdi
	rolq	%r9
	xorq	%r15, %r9
	xorq	%r9, %r12
	xorq	%r9, -120(%rsp)
	xorq	%r9, -72(%rsp)
	xorq	%r9, (%rsp)
	xorq	-40(%rsp), %r9
	movq	-112(%rsp), %r10
	xorq	%rbx, %r10
	rolq	$43, %r10
	xorq	%r13, %rdx
	xorq	%rdi, %rsi
	movq	-8(%rsp), %r15
	xorq	%r8, %r15
	rolq	$44, %rsi
	rolq	$21, %r15
	rolq	$14, %r12
	movq	%r10, %rcx
	notq	%rcx
	andq	%r15, %rcx
	xorq	%rsi, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rdx, %rcx
	notq	%rcx
	andq	%rsi, %rcx
	movq	%rsi, %rax
	notq	%rax
	movq	%r12, %r11
	notq	%r11
	andq	%r10, %rax
	andq	%rdx, %r11
	xorq	%r15, %r11
	movq	%r15, %rsi
	movq	%rcx, %r15
	notq	%rsi
	andq	%r12, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 24(%rsp)
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1(%rip), %rsi
	movq	64(%rsp), %rcx
	xorq	(%rcx,%rsi), %rax
	xorq	%r12, %r15
	movq	%r15, -8(%rsp)
	xorq	%rdx, %rax
	movq	%rax, -40(%rsp)
	movq	-64(%rsp), %r10
	xorq	%r13, %r10
	movq	%r13, %r15
	movq	8(%rsp), %rcx
	xorq	%r8, %rcx
	rolq	$3, %r10
	rolq	$28, %rcx
	movq	-88(%rsp), %r14
	movq	%rdi, %r13
	xorq	%rdi, %r14
	xorq	%rbx, %rbp
	rolq	$45, %r14
	rolq	$61, %rbp
	movq	-120(%rsp), %rsi
	rolq	$20, %rsi
	movq	%rsi, %rax
	notq	%rax
	andq	%r10, %rax
	movq	%rax, %rdx
	movq	%r14, %rax
	notq	%rax
	andq	%rbp, %rax
	xorq	%r10, %rax
	movq	%rax, -112(%rsp)
	notq	%r10
	movq	%rbp, %rax
	notq	%rax
	andq	%r14, %r10
	andq	%rcx, %rax
	xorq	%r14, %rax
	movq	%rax, 32(%rsp)
	xorq	%rcx, %rdx
	movq	%rdx, -88(%rsp)
	notq	%rcx
	andq	%rsi, %rcx
	xorq	%rbp, %rcx
	movq	%rcx, -80(%rsp)
	xorq	%rsi, %r10
	movq	%r10, -120(%rsp)
	movq	-96(%rsp), %rsi
	xorq	%rbx, %rsi
	movq	-24(%rsp), %rdi
	xorq	%rbx, %rdi
	xorq	72(%rsp), %rbx
	movq	-48(%rsp), %rcx
	xorq	%r15, %rcx
	movq	%r15, %rdx
	rolq	$15, %rdi
	rolq	$36, %rcx
	movq	48(%rsp), %r12
	movq	%r13, %r14
	xorq	%r13, %r12
	movq	-32(%rsp), %r10
	xorq	%r8, %r10
	movq	%r8, %rbp
	rolq	$10, %r12
	rolq	$56, %r10
	movq	%r10, -32(%rsp)
	movq	(%rsp), %rax
	rolq	$27, %rax
	movq	%rcx, %r8
	notq	%r8
	andq	%r12, %r8
	movq	%rdi, %r13
	notq	%r13
	andq	%r10, %r13
	xorq	%r12, %r13
	notq	%r12
	movq	%r10, %r15
	notq	%r15
	andq	%rdi, %r12
	andq	%rax, %r15
	xorq	%rdi, %r15
	movq	%r15, 8(%rsp)
	xorq	%rax, %r8
	movq	%r8, 40(%rsp)
	xorq	%rcx, %r12
	notq	%rax
	andq	%rcx, %rax
	movq	%rax, (%rsp)
	movq	%rsi, %rcx
	rolq	$6, %rcx
	movq	80(%rsp), %rsi
	xorq	%r14, %rsi
	movq	-128(%rsp), %r8
	movq	%rbp, %rdi
	xorq	%rbp, %r8
	rolq	%rsi
	rolq	$25, %r8
	movq	%r8, -128(%rsp)
	movq	-72(%rsp), %rax
	rolq	$8, %rax
	movq	56(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%rcx, %r15
	movq	%rcx, %r10
	notq	%r15
	andq	%r8, %r15
	xorq	%rsi, %r15
	movq	%r15, -96(%rsp)
	movq	%r8, %rcx
	notq	%rcx
	movq	%rbp, %r15
	notq	%r15
	andq	%rax, %rcx
	andq	%rsi, %r15
	notq	%rsi
	andq	%r10, %rsi
	movq	%rsi, %r8
	xorq	%r10, %rcx
	xorq	-104(%rsp), %rdi
	xorq	-56(%rsp), %rdx
	xorq	%rax, %r15
	movq	%rax, %rsi
	notq	%rsi
	xorq	%rbp, %r8
	movq	%r8, -104(%rsp)
	andq	%rbp, %rsi
	rolq	$62, %rbx
	movq	%rdi, %rbp
	rolq	$55, %rbp
	rolq	$41, %rdx
	rolq	$39, %r9
	xorq	-16(%rsp), %r14
	rolq	$2, %r14
	movq	(%rsp), %rdi
	xorq	-32(%rsp), %rdi
	movq	%rbp, %r10
	notq	%r10
	andq	%r9, %r10
	movq	%rdx, %rax
	notq	%rax
	andq	%r14, %rax
	xorq	%r9, %rax
	notq	%r9
	andq	%rdx, %r9
	movq	%r14, %r8
	notq	%r8
	andq	%rbx, %r8
	xorq	%rdx, %r8
	xorq	%rbx, %r10
	xorq	%rbp, %r9
	notq	%rbx
	andq	%rbp, %rbx
	xorq	-128(%rsp), %rsi
	xorq	%r14, %rbx
	movq	%rcx, -72(%rsp)
	xorq	-120(%rsp), %rcx
	movq	%r9, -16(%rsp)
	xorq	%r9, %rcx
	movq	16(%rsp), %r9
	movq	%r12, -48(%rsp)
	xorq	%r12, %r9
	xorq	%rcx, %r9
	movq	24(%rsp), %rcx
	xorq	-112(%rsp), %rcx
	movq	%r13, -56(%rsp)
	xorq	%rax, %r13
	xorq	%rsi, %rcx
	xorq	%rcx, %r13
	movq	8(%rsp), %rdx
	movq	%rdx, %rcx
	xorq	32(%rsp), %rcx
	xorq	%r11, %rcx
	movq	%r15, -64(%rsp)
	movq	%r15, %rbp
	movq	%r8, -24(%rsp)
	xorq	%r8, %rbp
	movq	%rdx, %r8
	xorq	%rcx, %rbp
	movq	-80(%rsp), %r14
	movq	-8(%rsp), %rcx
	movq	%rcx, %r15
	xorq	%rcx, %r14
	movq	-104(%rsp), %rcx
	xorq	%rbx, %rcx
	movq	%rdi, -128(%rsp)
	xorq	%rdi, %r14
	xorq	%r14, %rcx
	movq	%r10, %r14
	xorq	-96(%rsp), %r14
	xorq	-88(%rsp), %r14
	xorq	40(%rsp), %r14
	xorq	-40(%rsp), %r14
	movq	64(%rsp), %rdx
	addq	$16, %rdx
	movq	%rdx, %rdi
	cmpq	$200, %rdx
	jne	.LBB81_1
	movq	88(%rsp), %rcx
	movq	-40(%rsp), %rdi
	movq	%rdi, (%rcx)
	movq	-120(%rsp), %rdi
	movq	%rdi, 48(%rcx)
	movq	%rsi, 96(%rcx)
	movq	%r8, 144(%rcx)
	movq	%rbx, 192(%rcx)
	movq	%r11, 24(%rcx)
	movq	-80(%rsp), %rdx
	movq	%rdx, 72(%rcx)
	movq	-96(%rsp), %rdx
	movq	%rdx, 80(%rcx)
	movq	-48(%rsp), %rdx
	movq	%rdx, 128(%rcx)
	movq	%rax, 176(%rcx)
	movq	16(%rsp), %rax
	movq	%rax, 8(%rcx)
	movq	-112(%rsp), %rax
	movq	%rax, 56(%rcx)
	movq	-64(%rsp), %rax
	movq	%rax, 104(%rcx)
	movq	-128(%rsp), %rax
	movq	%rax, 152(%rcx)
	movq	%r10, 160(%rcx)
	movq	%r15, 32(%rcx)
	movq	-88(%rsp), %rax
	movq	%rax, 40(%rcx)
	movq	-72(%rsp), %rax
	movq	%rax, 88(%rcx)
	movq	-56(%rsp), %rax
	movq	%rax, 136(%rcx)
	movq	-24(%rsp), %rax
	movq	%rax, 184(%rcx)
	movq	24(%rsp), %rax
	movq	%rax, 16(%rcx)
	movq	32(%rsp), %rax
	movq	%rax, 64(%rcx)
	movq	-104(%rsp), %rax
	movq	%rax, 112(%rcx)
	movq	40(%rsp), %rax
	movq	%rax, 120(%rcx)
	movq	-16(%rsp), %rax
	movq	%rax, 168(%rcx)
	addq	$112, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end81:
	.size	_RNvCsndc0WgnAaH_9keccak2568keccak_f, .Lfunc_end81-_RNvCsndc0WgnAaH_9keccak2568keccak_f
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,"ax",@progbits
	.p2align	4
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update:
.Lfunc_begin82:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, %r14
	leaq	200(%rdi), %r13
	movq	336(%rdi), %rdi
	movq	memcpy@GOTPCREL(%rip), %rbp
	jmp	.LBB82_1
	.p2align	4
.LBB82_5:
	subq	%r12, %rbx
	addq	%r12, %r15
	testq	%rbx, %rbx
	je	.LBB82_6
.LBB82_1:
	movl	$136, %r12d
	subq	%rdi, %r12
	cmpq	%r12, %rbx
	cmovbq	%rbx, %r12
	leaq	(%r12,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB82_7
	cmpq	$137, %rsi
	jae	.LBB82_7
	addq	%r13, %rdi
	movq	%r15, %rsi
	movq	%r12, %rdx
	callq	*%rbp
	movq	336(%r14), %rdi
	addq	%r12, %rdi
	movq	%rdi, 336(%r14)
	cmpq	$136, %rdi
	jne	.LBB82_5
	movq	200(%r14), %rax
	movq	%rax, 40(%rsp)
	movq	208(%r14), %rcx
	movq	216(%r14), %rdx
	movq	224(%r14), %rsi
	movq	232(%r14), %rdi
	movq	240(%r14), %r8
	movq	248(%r14), %r9
	movq	256(%r14), %r10
	movq	264(%r14), %r11
	movq	272(%r14), %r13
	movq	280(%r14), %rbp
	movq	288(%r14), %rax
	movq	%rax, 48(%rsp)
	movq	296(%r14), %rax
	movq	%rax, 32(%rsp)
	movq	304(%r14), %rax
	movq	%rax, 24(%rsp)
	movq	312(%r14), %rax
	movq	%rax, 16(%rsp)
	movq	320(%r14), %rax
	movq	%rax, 8(%rsp)
	movq	328(%r14), %rax
	movq	%rax, (%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, (%r14)
	xorq	%rcx, 8(%r14)
	xorq	%rdx, 16(%r14)
	xorq	%rsi, 24(%r14)
	xorq	%rdi, 32(%r14)
	xorq	%r8, 40(%r14)
	xorq	%r9, 48(%r14)
	xorq	%r10, 56(%r14)
	xorq	%r11, 64(%r14)
	xorq	%r13, 72(%r14)
	leaq	200(%r14), %r13
	xorq	%rbp, 80(%r14)
	movq	memcpy@GOTPCREL(%rip), %rbp
	movq	48(%rsp), %rax
	xorq	%rax, 88(%r14)
	movq	32(%rsp), %rax
	xorq	%rax, 96(%r14)
	movq	24(%rsp), %rax
	xorq	%rax, 104(%r14)
	movq	16(%rsp), %rax
	xorq	%rax, 112(%r14)
	movq	8(%rsp), %rax
	xorq	%rax, 120(%r14)
	movq	(%rsp), %rax
	xorq	%rax, 128(%r14)
	movq	%r14, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 336(%r14)
	xorl	%edi, %edi
	jmp	.LBB82_5
.LBB82_6:
	movq	%r14, %rax
	addq	$56, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB82_7:
	.cfi_def_cfa_offset 112
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.11(%rip), %rcx
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.Lfunc_end82:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update, .Lfunc_end82-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,"ax",@progbits
	.p2align	4
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize:
.Lfunc_begin83:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	subq	$344, %rsp
	.cfi_def_cfa_offset 384
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r15
	movq	%rdi, %rbx
	leaq	144(%rsp), %rdi
	movl	$200, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	336(%r15), %r14
	cmpq	$137, %r14
	jae	.LBB83_3
	cmpq	$136, %r14
	je	.LBB83_4
	addq	$200, %r15
	leaq	8(%rsp), %r12
	movl	$136, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	*memcpy@GOTPCREL(%rip)
	xorb	$1, 8(%rsp,%r14)
	xorb	$-128, 143(%rsp)
	movq	8(%rsp), %rax
	xorq	%rax, 144(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 152(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 160(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 168(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 176(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 184(%rsp)
	movq	56(%rsp), %rax
	xorq	%rax, 192(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 200(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	80(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	88(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	96(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	104(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	112(%rsp), %rax
	xorq	%rax, 248(%rsp)
	movq	120(%rsp), %rax
	xorq	%rax, 256(%rsp)
	movq	128(%rsp), %rax
	xorq	%rax, 264(%rsp)
	movq	136(%rsp), %rax
	xorq	%rax, 272(%rsp)
	leaq	144(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	168(%rsp), %rax
	movq	%rax, 24(%rbx)
	movq	160(%rsp), %rax
	movq	%rax, 16(%rbx)
	movq	144(%rsp), %rax
	movq	152(%rsp), %rcx
	movq	%rcx, 8(%rbx)
	movq	%rax, (%rbx)
	addq	$344, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB83_3:
	.cfi_def_cfa_offset 384
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.12(%rip), %rcx
	movl	$136, %edx
	xorl	%edi, %edi
	movq	%r14, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB83_4:
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.8(%rip), %rdi
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.9(%rip), %rdx
	movl	$99, %esi
	callq	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt
.Lfunc_end83:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize, .Lfunc_end83-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	.cfi_endproc

	.section	.text._RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,"ax",@progbits
	.p2align	4
	.type	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,@function
_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read:
.Lfunc_begin84:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$1880, %rsp
	.cfi_def_cfa_offset 1936
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	8(%rsi), %r12
	cmpq	$15, %r12
	jbe	.LBB84_22
	movq	%rsi, %r14
	movq	%rdi, 16(%rsp)
	leaq	24(%rsp), %rsi
	movq	(%r14), %r11
	leaq	-16(%r12), %rax
	shrq	$4, %rax
	xorl	%ecx, %ecx
	movq	%rax, %rdx
	xorl	%edi, %edi
	.p2align	4
.LBB84_2:
	testq	%rdx, %rdx
	je	.LBB84_22
	movq	%r12, %rbx
	leaq	(%r11,%rcx), %r13
	addq	$16, %r13
	leaq	32(%r11,%rcx), %r8
	addq	$-32, %r12
	movq	%r8, (%r14)
	movq	%r12, 8(%r14)
	movq	(%r13), %r9
	movq	8(%r13), %r10
	movq	%r10, 8(%rsi,%rcx)
	movq	%r9, (%rsi,%rcx)
	leaq	1(%rdi), %r9
	cmpq	%rax, %r9
	je	.LBB84_22
	leaq	(%r11,%rcx), %r15
	addq	$48, %r15
	leaq	-48(%rbx), %rbp
	movq	%r15, (%r14)
	movq	%rbp, 8(%r14)
	movq	(%r8), %r9
	movq	8(%r8), %r8
	movq	%r8, 24(%rsi,%rcx)
	movq	%r9, 16(%rsi,%rcx)
	addq	$2, %rdi
	addq	$32, %rcx
	addq	$-2, %rdx
	cmpq	$58, %rdi
	jne	.LBB84_2
	movq	%r11, 8(%rsp)
	leaq	952(%rsp), %rdi
	movl	$928, %edx
	callq	*memcpy@GOTPCREL(%rip)
	cmpq	$15, %rbp
	jbe	.LBB84_22
	movq	(%r15), %rax
	movq	8(%r15), %rcx
	movq	%rcx, 32(%rsp)
	movq	%rax, 24(%rsp)
	andq	$-16, %rbp
	cmpq	$16, %rbp
	je	.LBB84_22
	movq	48(%r13), %rax
	movq	56(%r13), %rcx
	movq	%rcx, 48(%rsp)
	movq	%rax, 40(%rsp)
	cmpq	$32, %rbp
	je	.LBB84_22
	movq	64(%r13), %rax
	movq	72(%r13), %rcx
	movq	%rcx, 64(%rsp)
	movq	%rax, 56(%rsp)
	cmpq	$48, %rbp
	je	.LBB84_22
	movq	80(%r13), %rax
	movq	88(%r13), %rcx
	movq	%rcx, 80(%rsp)
	movq	%rax, 72(%rsp)
	cmpq	$64, %rbp
	je	.LBB84_22
	movq	96(%r13), %rax
	movq	104(%r13), %rcx
	movq	%rcx, 96(%rsp)
	movq	%rax, 88(%rsp)
	cmpq	$80, %rbp
	je	.LBB84_22
	movq	112(%r13), %rax
	movq	120(%r13), %rcx
	movq	%rcx, 112(%rsp)
	movq	%rax, 104(%rsp)
	cmpq	$96, %rbp
	je	.LBB84_22
	movq	128(%r13), %rax
	movq	136(%r13), %rcx
	movq	%rcx, 128(%rsp)
	movq	%rax, 120(%rsp)
	cmpq	$112, %rbp
	je	.LBB84_22
	movq	144(%r13), %rax
	movq	152(%r13), %rcx
	movq	%rcx, 144(%rsp)
	movq	%rax, 136(%rsp)
	andq	$-16, %r12
	cmpq	$144, %r12
	je	.LBB84_22
	movq	160(%r13), %rax
	movq	168(%r13), %rcx
	movq	%rcx, 160(%rsp)
	movq	%rax, 152(%rsp)
	cmpq	$144, %rbp
	je	.LBB84_22
	movq	176(%r13), %rax
	movq	184(%r13), %rcx
	movq	%rcx, 176(%rsp)
	movq	%rax, 168(%rsp)
	cmpq	$160, %rbp
	je	.LBB84_22
	movq	192(%r13), %rax
	movq	200(%r13), %rcx
	movq	%rcx, 192(%rsp)
	movq	%rax, 184(%rsp)
	cmpq	$176, %rbp
	je	.LBB84_22
	movq	208(%r13), %rax
	movq	216(%r13), %rcx
	movq	%rcx, 208(%rsp)
	movq	%rax, 200(%rsp)
	cmpq	$192, %rbp
	je	.LBB84_22
	movq	224(%r13), %rax
	movq	232(%r13), %rcx
	movq	%rcx, 224(%rsp)
	movq	%rax, 216(%rsp)
	cmpq	$208, %rbp
	je	.LBB84_22
	movq	240(%r13), %rax
	movq	248(%r13), %rcx
	movq	%rcx, 240(%rsp)
	movq	%rax, 232(%rsp)
	cmpq	$224, %rbp
	je	.LBB84_22
	movq	256(%r13), %rax
	movq	264(%r13), %rcx
	movq	%rcx, 256(%rsp)
	movq	%rax, 248(%rsp)
	cmpq	$240, %rbp
	je	.LBB84_22
	addq	$-16, %rbx
	leaq	288(%r13), %rax
	addq	$-288, %rbx
	movq	%rax, (%r14)
	movq	%rbx, 8(%r14)
	movq	272(%r13), %rax
	movq	280(%r13), %rcx
	movq	%rcx, 272(%rsp)
	movq	%rax, 264(%rsp)
	leaq	24(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	movl	$256, %edx
	movq	16(%rsp), %r14
	movq	%r14, %rdi
	callq	*%rbx
	movq	8(%rsp), %rcx
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	movq	%rcx, 1192(%r14)
	movq	%rax, 1184(%r14)
	addq	$256, %r14
	leaq	952(%rsp), %rsi
	movl	$928, %edx
	movq	%r14, %rdi
	callq	*%rbx
	addq	$1880, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB84_22:
	.cfi_def_cfa_offset 1936
	leaq	.Lanon.2110530ee3456a504423839f2911ae7b.2(%rip), %rdi
	callq	_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed
.Lfunc_end84:
	.size	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read, .Lfunc_end84-_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	.cfi_endproc

	.section	.text._RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,"ax",@progbits
	.p2align	4
	.type	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,@function
_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf:
.Lfunc_begin85:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$2712, %rsp
	.cfi_def_cfa_offset 2768
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r14
	movq	%r8, %r15
	movq	%rsi, %r13
	movq	%rdi, 96(%rsp)
	movq	2768(%rsp), %rbx
	movl	%ecx, 52(%rsp)
	movl	%ecx, 112(%rsp)
	movq	%rdx, %rax
	movq	%rdx, 8(%rsp)
	shll	$7, %eax
	movb	%al, 118(%rsp)
	movw	$0, 116(%rsp)
	movb	$12, 119(%rsp)
	movq	$0, 120(%rsp)
	leaq	2008(%rsp), %r12
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%r13, 104(%rsp)
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r12, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	120(%rsp), %rdx
	movq	%rdx, %rax
	shrq	$52, %rax
	jne	.LBB85_25
	movq	112(%rsp), %rsi
	movabsq	$1229782938247303441, %rax
	movq	%rsi, %rcx
	andq	%rax, %rcx
	movq	%rsi, %rdi
	shrq	$2, %rdi
	andq	%rax, %rdi
	addq	%rcx, %rdi
	movq	%rdi, %r8
	shrq	$4, %r8
	addq	%rdi, %r8
	movabsq	$1085102592571150095, %rax
	andq	%rax, %r8
	movabsq	$72340172838076673, %rcx
	imulq	%rcx, %r8
	shrq	$56, %r8
	movabsq	$300239975158033, %rdi
	movq	%rdx, %r9
	andq	%rdi, %r9
	movq	%rdx, %r10
	shrq	$2, %r10
	andq	%rdi, %r10
	addq	%r9, %r10
	movq	%r10, %rdi
	shrq	$4, %rdi
	addq	%r10, %rdi
	andq	%rax, %rdi
	imulq	%rcx, %rdi
	shrq	$56, %rdi
	addl	%r8d, %edi
	movabsq	$3002399751580330, %r8
	andq	%rdx, %r8
	movabsq	$-6148914691236517206, %r10
	andq	%rsi, %r10
	movq	%r10, %r9
	shrq	%r9
	subq	%r9, %r10
	movabsq	$3689348814741910323, %r11
	movq	%r10, %r9
	andq	%r11, %r9
	shrq	$2, %r10
	andq	%r11, %r10
	addq	%r9, %r10
	movq	%r10, %r9
	shrq	$4, %r9
	addq	%r10, %r9
	andq	%rax, %r9
	imulq	%rcx, %r9
	shrq	$56, %r9
	movq	%r8, %r10
	shrq	%r10
	subq	%r10, %r8
	movq	%r8, %r10
	andq	%r11, %r10
	shrq	$2, %r8
	andq	%r11, %r8
	addq	%r10, %r8
	movq	%r8, %r10
	shrq	$4, %r10
	addq	%r8, %r10
	andq	%rax, %r10
	imulq	%rcx, %r10
	shrq	$56, %r10
	addl	%r9d, %r10d
	leal	(%rdi,%r10,2), %eax
	cmpl	$106, %eax
	jne	.LBB85_25
	movq	8(%rsp), %rax
	shll	$23, %eax
	movq	%rax, 8(%rsp)
	leaq	615(%rsp), %rdi
	xorl	%eax, %eax
	.p2align	4
.LBB85_3:
	movq	%rsi, %r8
	movl	%eax, %ecx
	shrdq	%cl, %rdx, %r8
	movq	%rdx, %r9
	shrq	%cl, %r9
	testb	$64, %al
	cmoveq	%r8, %r9
	leal	2(%rax), %ecx
	movq	%rsi, %r8
	shrdq	%cl, %rdx, %r8
	andb	$3, %r9b
	movb	%r9b, -1(%rdi)
	movq	%rdx, %r9
	shrq	%cl, %r9
	testb	$64, %cl
	cmoveq	%r8, %r9
	andb	$3, %r9b
	movb	%r9b, (%rdi)
	addq	$4, %rax
	addq	$2, %rdi
	cmpq	$116, %rax
	jne	.LBB85_3
	xorl	%edx, %edx
	movq	8(%rsp), %rax
	shrl	$16, %eax
	movl	%eax, 48(%rsp)
	leaq	112(%rsp), %r12
	movq	memset@GOTPCREL(%rip), %rbx
	movq	memcpy@GOTPCREL(%rip), %r13
	jmp	.LBB85_5
.LBB85_25:
	movq	96(%rsp), %rax
	movb	$0, (%rax)
.LBB85_26:
	addq	$2712, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
	.p2align	4
.LBB85_23:
	.cfi_def_cfa_offset 2768
	movq	80(%rsp), %rax
	movq	88(%rsp), %rcx
	movq	456(%rsp), %rsi
	movq	%rax, 1080(%rsp,%rsi)
	movq	%rcx, 1088(%rsp,%rsi)
	incq	%rdx
	cmpq	$58, %rdx
	je	.LBB85_24
.LBB85_5:
	movzbl	614(%rsp,%rdx), %r14d
	movq	%rdx, %rsi
	shlq	$4, %rsi
	movq	2776(%rsp), %rcx
	movq	(%rcx,%rsi), %rax
	movq	%rsi, 456(%rsp)
	movq	8(%rcx,%rsi), %rcx
	movq	%rax, 80(%rsp)
	movq	%rcx, 88(%rsp)
	cmpq	$2, %r14
	ja	.LBB85_23
	movq	%rdx, 464(%rsp)
	.p2align	4
.LBB85_7:
	movq	80(%rsp), %rax
	movq	88(%rsp), %rcx
	movq	%rcx, 680(%rsp)
	movq	%rax, 672(%rsp)
	movq	%rdx, 688(%rsp)
	movq	$0, 696(%rsp)
	movl	%r14d, %eax
	shlb	$5, %al
	incb	%al
	movl	52(%rsp), %ecx
	movl	%ecx, 472(%rsp)
	movl	48(%rsp), %ecx
	movb	%cl, 478(%rsp)
	movq	8(%rsp), %rcx
	movw	%cx, 476(%rsp)
	movb	%al, 479(%rsp)
	movq	$0, 480(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	104(%rsp), %rcx
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	312(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	448(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 448(%rsp)
	cmpq	$136, %rdi
	jne	.LBB85_9
	movq	312(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	352(%rsp), %r8
	movq	360(%rsp), %r9
	movq	368(%rsp), %r10
	movq	376(%rsp), %r11
	movq	384(%rsp), %rbx
	movq	%r14, 56(%rsp)
	movq	392(%rsp), %r14
	movq	400(%rsp), %r15
	movq	408(%rsp), %r12
	movq	416(%rsp), %rbp
	movq	%rbp, 40(%rsp)
	movq	424(%rsp), %rbp
	movq	432(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	440(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 112(%rsp)
	xorq	%rcx, 120(%rsp)
	xorq	%rdx, 128(%rsp)
	xorq	%rsi, 136(%rsp)
	xorq	%rdi, 144(%rsp)
	xorq	%r8, 152(%rsp)
	xorq	%r9, 160(%rsp)
	xorq	%r10, 168(%rsp)
	xorq	%r11, 176(%rsp)
	xorq	%rbx, 184(%rsp)
	xorq	%r14, 192(%rsp)
	movq	56(%rsp), %r14
	xorq	%r15, 200(%rsp)
	xorq	%r12, 208(%rsp)
	leaq	112(%rsp), %r12
	movq	40(%rsp), %rax
	xorq	%rax, 216(%rsp)
	xorq	%rbp, 224(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 448(%rsp)
	xorl	%edi, %edi
.LBB85_9:
	incq	%r14
	movq	%r14, 56(%rsp)
	movl	$16, %r14d
	leaq	472(%rsp), %rbx
	jmp	.LBB85_10
	.p2align	4
.LBB85_14:
	subq	%r15, %r14
	addq	%r15, %rbx
	testq	%r14, %r14
	je	.LBB85_15
.LBB85_10:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r14
	cmovbq	%r14, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB85_27
	cmpq	$137, %rsi
	jae	.LBB85_27
	leaq	312(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r13
	movq	448(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 448(%rsp)
	cmpq	$136, %rdi
	jne	.LBB85_14
	movq	312(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	352(%rsp), %r8
	movq	360(%rsp), %r9
	movq	368(%rsp), %r10
	movq	376(%rsp), %r11
	movq	384(%rsp), %r12
	movq	392(%rsp), %rbp
	movq	400(%rsp), %r13
	movq	408(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	416(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	424(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	432(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	440(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 112(%rsp)
	xorq	%rcx, 120(%rsp)
	xorq	%rdx, 128(%rsp)
	xorq	%rsi, 136(%rsp)
	xorq	%rdi, 144(%rsp)
	xorq	%r8, 152(%rsp)
	xorq	%r9, 160(%rsp)
	xorq	%r10, 168(%rsp)
	xorq	%r11, 176(%rsp)
	xorq	%r12, 184(%rsp)
	leaq	112(%rsp), %r12
	xorq	%rbp, 192(%rsp)
	xorq	%r13, 200(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r13
	movq	40(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 448(%rsp)
	xorl	%edi, %edi
	jmp	.LBB85_14
	.p2align	4
.LBB85_15:
	movl	$344, %edx
	leaq	704(%rsp), %rdi
	movq	%r12, %rsi
	callq	*%r13
	movl	$32, %r12d
	movq	1040(%rsp), %r15
	leaq	672(%rsp), %rbx
	jmp	.LBB85_16
	.p2align	4
.LBB85_20:
	subq	%r14, %r12
	addq	%r14, %rbx
	testq	%r12, %r12
	je	.LBB85_21
.LBB85_16:
	movl	$136, %r14d
	subq	%r15, %r14
	cmpq	%r14, %r12
	cmovbq	%r12, %r14
	leaq	(%r14,%r15), %rsi
	cmpq	%r15, %rsi
	jb	.LBB85_28
	cmpq	$137, %rsi
	jae	.LBB85_28
	leaq	904(%rsp), %rax
	addq	%rax, %r15
	movq	%r15, %rdi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	*%r13
	movq	1040(%rsp), %r15
	addq	%r14, %r15
	movq	%r15, 1040(%rsp)
	cmpq	$136, %r15
	jne	.LBB85_20
	movq	904(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	912(%rsp), %rcx
	movq	920(%rsp), %rdx
	movq	928(%rsp), %rsi
	movq	936(%rsp), %rdi
	movq	944(%rsp), %r8
	movq	952(%rsp), %r9
	movq	960(%rsp), %r10
	movq	968(%rsp), %r11
	movq	976(%rsp), %r15
	movq	984(%rsp), %r13
	movq	992(%rsp), %rbp
	movq	1000(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	1008(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	1016(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	1024(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	1032(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 704(%rsp)
	xorq	%rcx, 712(%rsp)
	xorq	%rdx, 720(%rsp)
	xorq	%rsi, 728(%rsp)
	xorq	%rdi, 736(%rsp)
	xorq	%r8, 744(%rsp)
	xorq	%r9, 752(%rsp)
	xorq	%r10, 760(%rsp)
	xorq	%r11, 768(%rsp)
	xorq	%r15, 776(%rsp)
	xorq	%r13, 784(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r13
	xorq	%rbp, 792(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 800(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 808(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 816(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 824(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 832(%rsp)
	leaq	704(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 1040(%rsp)
	xorl	%r15d, %r15d
	jmp	.LBB85_20
	.p2align	4
.LBB85_21:
	movl	$200, %edx
	leaq	112(%rsp), %r12
	movq	%r12, %rdi
	leaq	704(%rsp), %rsi
	callq	*%r13
	cmpq	$137, %r15
	jae	.LBB85_29
	movl	$136, %edx
	leaq	472(%rsp), %r14
	movq	%r14, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %rbx
	callq	*%rbx
	movq	%r14, %rdi
	leaq	904(%rsp), %rsi
	movq	%r15, %rdx
	callq	*%r13
	xorb	$1, 472(%rsp,%r15)
	xorb	$-128, 607(%rsp)
	movq	472(%rsp), %rax
	xorq	%rax, 112(%rsp)
	movq	480(%rsp), %rax
	xorq	%rax, 120(%rsp)
	movq	488(%rsp), %rax
	xorq	%rax, 128(%rsp)
	movq	496(%rsp), %rax
	xorq	%rax, 136(%rsp)
	movq	504(%rsp), %rax
	xorq	%rax, 144(%rsp)
	movq	512(%rsp), %rax
	xorq	%rax, 152(%rsp)
	movq	520(%rsp), %rax
	xorq	%rax, 160(%rsp)
	movq	528(%rsp), %rax
	xorq	%rax, 168(%rsp)
	movq	536(%rsp), %rax
	xorq	%rax, 176(%rsp)
	movq	544(%rsp), %rax
	xorq	%rax, 184(%rsp)
	movq	552(%rsp), %rax
	xorq	%rax, 192(%rsp)
	movq	560(%rsp), %rax
	xorq	%rax, 200(%rsp)
	movq	568(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	576(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	584(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	592(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	600(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	136(%rsp), %rax
	movq	%rax, 496(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	%rax, 472(%rsp)
	movq	%rax, 80(%rsp)
	movq	%rcx, 88(%rsp)
	movq	56(%rsp), %r14
	cmpq	$3, %r14
	movq	464(%rsp), %rdx
	jne	.LBB85_7
	jmp	.LBB85_23
.LBB85_27:
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.11(%rip), %rcx
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB85_28:
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.11(%rip), %rcx
	movl	$136, %edx
	movq	%r15, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB85_24:
	movl	52(%rsp), %eax
	movl	%eax, 112(%rsp)
	movq	8(%rsp), %rax
	movw	%ax, 116(%rsp)
	movl	48(%rsp), %eax
	movb	%al, 118(%rsp)
	movb	$2, 119(%rsp)
	movq	$0, 120(%rsp)
	leaq	2352(%rsp), %rbx
	movl	$344, %edx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%rbx, %rdi
	movq	104(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%rbx, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	1080(%rsp), %rsi
	movl	$928, %edx
	movq	%rbx, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	1048(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movzwl	670(%rsp), %eax
	movw	%ax, 168(%rsp)
	movq	662(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	654(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	646(%rsp), %rax
	movq	%rax, 144(%rsp)
	movq	638(%rsp), %rax
	movq	%rax, 136(%rsp)
	movq	630(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	614(%rsp), %rax
	movq	622(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	%rax, 112(%rsp)
	movq	1048(%rsp), %rax
	movq	1056(%rsp), %rcx
	movq	%rax, 170(%rsp)
	movq	%rcx, 178(%rsp)
	movq	96(%rsp), %rbx
	leaq	1(%rbx), %rdi
	leaq	112(%rsp), %rsi
	movl	$74, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movb	$1, (%rbx)
	jmp	.LBB85_26
.LBB85_29:
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.12(%rip), %rcx
	movl	$136, %edx
	xorl	%edi, %edi
	movq	%r15, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.Lfunc_end85:
	.size	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf, .Lfunc_end85-_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	.cfi_endproc

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1,@object
	.section	.rodata..Lanon.5ef9b7c546f4dc64388b910df55ec241.1,"a",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.1:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1, 192

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.3,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.5ef9b7c546f4dc64388b910df55ec241.3:
	.asciz	"crates/keccak256/src/lib.rs"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.3, 28

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.8,@object
	.section	.rodata..Lanon.5ef9b7c546f4dc64388b910df55ec241.8,"a",@progbits
.Lanon.5ef9b7c546f4dc64388b910df55ec241.8:
	.ascii	"a final block holds fewer than RATE message bytes"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.8, 49

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.9,@object
	.section	.data.rel.ro..Lanon.5ef9b7c546f4dc64388b910df55ec241.9,"aw",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.9:
	.quad	.Lanon.5ef9b7c546f4dc64388b910df55ec241.3
	.asciz	"\033\000\000\000\000\000\000\000~\000\000\000\005\000\000"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.9, 24

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.11,@object
	.section	.data.rel.ro..Lanon.5ef9b7c546f4dc64388b910df55ec241.11,"aw",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.11:
	.quad	.Lanon.5ef9b7c546f4dc64388b910df55ec241.3
	.asciz	"\033\000\000\000\000\000\000\000\245\000\000\000\025\000\000"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.11, 24

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.12,@object
	.section	.data.rel.ro..Lanon.5ef9b7c546f4dc64388b910df55ec241.12,"aw",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.12:
	.quad	.Lanon.5ef9b7c546f4dc64388b910df55ec241.3
	.asciz	"\033\000\000\000\000\000\000\000\262\000\000\0002\000\000"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.12, 24

	.type	.Lanon.2110530ee3456a504423839f2911ae7b.1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.2110530ee3456a504423839f2911ae7b.1:
	.asciz	"crates/lean_xmss/src/scheme.rs"
	.size	.Lanon.2110530ee3456a504423839f2911ae7b.1, 31

	.type	.Lanon.2110530ee3456a504423839f2911ae7b.2,@object
	.section	.data.rel.ro..Lanon.2110530ee3456a504423839f2911ae7b.2,"aw",@progbits
	.p2align	3, 0x0
.Lanon.2110530ee3456a504423839f2911ae7b.2:
	.quad	.Lanon.2110530ee3456a504423839f2911ae7b.1
	.asciz	"\036\000\000\000\000\000\000\000G\000\000\0002\000\000"
	.size	.Lanon.2110530ee3456a504423839f2911ae7b.2, 24
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
