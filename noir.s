	.file	"fake.c"
	.text
	.p2align 4
	.type	fib, @function
fib:
.LFB3:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	movl	%edi, %ebx
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	cmpl	$1, %edi
	je	.L1
.L2:
	leal	-1(%rdi), %eax
	xorl	%ebp, %ebp
	movl	%edi, %r15d
	movl	%eax, %edx
	movl	%ebp, %ebx
	movl	%edi, %ebp
	movl	%eax, %r14d
	andl	$-2, %edx
	subl	%edx, %r15d
	cmpl	%r15d, %ebp
	je	.L3
.L48:
	subl	$2, %ebp
	movl	%r14d, %ecx
	xorl	%r12d, %r12d
	movl	%ebp, %eax
	andl	$-2, %eax
	subl	%eax, %ecx
	movl	%r14d, %eax
	movl	%r15d, %r14d
	movl	%ecx, 56(%rsp)
	movl	%ebp, %ecx
	movl	%ebx, %ebp
	movl	%ecx, %ebx
.L4:
	movl	56(%rsp), %ecx
	leal	-1(%rax), %edx
	movl	%edx, %r15d
	cmpl	%ecx, %eax
	je	.L5
	subl	$2, %eax
	movl	%r15d, %ecx
	movl	%r12d, 44(%rsp)
	xorl	%r13d, %r13d
	movl	%eax, %edx
	movl	%eax, 48(%rsp)
	movl	%ebp, %r12d
	andl	$-2, %edx
	subl	%edx, %ecx
	movl	%r15d, %edx
	movl	%r14d, %r15d
	movl	%ecx, 60(%rsp)
.L6:
	movl	60(%rsp), %eax
	leal	-1(%rdx), %esi
	movl	%esi, %edi
	cmpl	%eax, %edx
	je	.L7
	subl	$2, %edx
	movl	%edi, %eax
	movl	%r13d, 52(%rsp)
	movl	%r12d, %ebp
	movl	%edx, %esi
	movl	%ebx, %r12d
	xorl	%r14d, %r14d
	movl	%r15d, %ebx
	andl	$-2, %esi
	subl	%esi, %eax
	movl	%edx, %esi
	movl	%eax, 64(%rsp)
.L8:
	movl	64(%rsp), %eax
	leal	-1(%rdi), %r8d
	cmpl	%eax, %edi
	je	.L9
	subl	$2, %edi
	movl	%r8d, %r15d
	movl	%ebp, %r9d
	movl	%ebx, %edx
	movl	%edi, %ecx
	movl	%esi, %r11d
	xorl	%r13d, %r13d
	movl	%r8d, %ebp
	andl	$-2, %ecx
	movl	%r12d, %ebx
	movl	%r14d, %esi
	subl	%ecx, %r15d
	movl	%edi, %ecx
.L10:
	leal	-1(%rbp), %r8d
	movl	%r8d, %eax
	cmpl	%r15d, %ebp
	je	.L11
	subl	$2, %ebp
	xorl	%r12d, %r12d
	movl	%r9d, %r10d
	movl	%esi, %r14d
	movl	%ebp, %edi
	andl	$-2, %edi
	subl	%edi, %r8d
	movl	%r8d, 24(%rsp)
.L12:
	movl	24(%rsp), %esi
	cmpl	%esi, %eax
	je	.L13
.L14:
	leal	-2(%rax), %edi
	leal	-3(%rax), %esi
	subl	$5, %eax
	movl	%edx, 12(%rsp)
	movl	%edi, %r8d
	movl	%esi, %r9d
	movl	%ecx, 16(%rsp)
	andl	$-2, %r8d
	subl	%r8d, %r9d
	movl	%esi, %r8d
	andl	$-2, %r8d
	movl	%r9d, 28(%rsp)
	movl	%ebp, %r9d
	movl	%ebx, %ebp
	subl	%r8d, %eax
	leal	1(%rsi), %r8d
	movl	%eax, 20(%rsp)
	xorl	%eax, %eax
	movl	%eax, %ebx
	cmpl	%esi, 28(%rsp)
	je	.L15
.L46:
	movl	%esi, 36(%rsp)
	movl	%esi, %edx
	xorl	%ecx, %ecx
	movl	%r10d, 32(%rsp)
	movl	%edi, %r10d
	movl	%ebp, 40(%rsp)
	movl	%ebx, %ebp
.L16:
	movl	%edx, %esi
	cmpl	$1, %edx
	je	.L39
	xorl	%ebx, %ebx
.L18:
	leal	-1(%rsi), %edi
	movl	%r10d, 92(%rsp)
	movl	%r9d, 88(%rsp)
	movl	%r11d, 84(%rsp)
	movl	%edx, 80(%rsp)
	movl	%ecx, 76(%rsp)
	movl	%r8d, 72(%rsp)
	movl	%esi, 68(%rsp)
	call	fib
	movl	68(%rsp), %esi
	movl	72(%rsp), %r8d
	addl	%eax, %ebx
	movl	76(%rsp), %ecx
	movl	80(%rsp), %edx
	subl	$2, %esi
	movl	84(%rsp), %r11d
	movl	88(%rsp), %r9d
	cmpl	$1, %esi
	movl	92(%rsp), %r10d
	jg	.L18
.L19:
	leal	-3(%r8), %edi
	subl	$2, %edx
	subl	$2, %r8d
	andl	$-2, %edi
	movl	%edx, %eax
	subl	%edi, %eax
	addl	%ebx, %eax
	addl	%eax, %ecx
	cmpl	$1, %r8d
	jne	.L16
	.p2align 4,,10
	.p2align 3
.L39:
.L20:
	movl	36(%rsp), %esi
	movl	%ebp, %ebx
	leal	1(%rcx), %edx
	movl	%r10d, %edi
	addl	%edx, %ebx
	movl	40(%rsp), %ebp
	movl	32(%rsp), %r10d
	leal	-2(%rsi), %edx
	cmpl	%edx, 20(%rsp)
	je	.L23
	movl	%edx, %esi
	leal	1(%rsi), %r8d
	cmpl	%esi, 28(%rsp)
	jne	.L46
.L15:
	movl	%ebx, %eax
	movl	12(%rsp), %edx
	movl	16(%rsp), %ecx
	movl	%ebp, %ebx
	leal	(%r8,%rax), %esi
	movl	%r9d, %ebp
.L22:
	movl	%edi, %eax
	addl	%esi, %r12d
	cmpl	$1, %edi
	jne	.L12
	movl	%r10d, %r9d
	movl	%r14d, %esi
	addl	$1, %r12d
	jmp	.L24
	.p2align 4,,10
	.p2align 3
.L13:
	movl	%r10d, %r9d
	movl	%r14d, %esi
	leal	-1(%rax,%r12), %r12d
.L24:
	addl	%r12d, %r13d
	cmpl	$1, %ebp
	jne	.L10
	movl	%esi, %r14d
	movl	%ebx, %r12d
	movl	%r9d, %ebp
	movl	%edx, %ebx
	movl	%r11d, %esi
	movl	%ecx, %edi
	addl	$1, %r13d
.L26:
	addl	%r13d, %r14d
	cmpl	$1, %edi
	jne	.L8
	movl	%ebx, %r15d
	movl	52(%rsp), %r13d
	movl	%r12d, %ebx
	movl	%esi, %edx
	movl	%ebp, %r12d
	addl	$1, %r14d
	jmp	.L28
	.p2align 4,,10
	.p2align 3
.L11:
	movl	%esi, %r14d
	movl	%ebx, %r12d
	movl	%r9d, %ebp
	movl	%edx, %ebx
	movl	%r11d, %esi
	movl	%ecx, %edi
	addl	%r8d, %r13d
	jmp	.L26
.L9:
	movl	52(%rsp), %r13d
	movl	%ebx, %r15d
	movl	%esi, %edx
	movl	%r12d, %ebx
	addl	%r8d, %r14d
	movl	%ebp, %r12d
.L28:
	addl	%r14d, %r13d
	cmpl	$1, %edx
	jne	.L6
	movl	%r12d, %ebp
	movl	48(%rsp), %eax
	movl	44(%rsp), %r12d
	movl	%r15d, %r14d
	addl	$1, %r13d
	jmp	.L30
	.p2align 4,,10
	.p2align 3
.L7:
	movl	%r12d, %ebp
	movl	48(%rsp), %eax
	movl	44(%rsp), %r12d
	movl	%r15d, %r14d
	addl	%esi, %r13d
.L30:
	addl	%r13d, %r12d
	cmpl	$1, %eax
	jne	.L4
	movl	%ebx, %eax
	addl	$1, %r12d
	movl	%ebp, %ebx
	movl	%r14d, %r15d
	movl	%eax, %ebp
	addl	%r12d, %ebx
	cmpl	$1, %ebp
	jne	.L47
.L38:
	leal	1(%rbx), %ebx
	jmp	.L1
	.p2align 4,,10
	.p2align 3
.L5:
.L32:
	movl	%ebx, %ecx
	addl	%edx, %r12d
	movl	%ebp, %ebx
	movl	%r14d, %r15d
	movl	%ecx, %ebp
	addl	%r12d, %ebx
	cmpl	$1, %ebp
	je	.L38
.L47:
	leal	-1(%rbp), %eax
	movl	%eax, %r14d
	cmpl	%r15d, %ebp
	jne	.L48
.L3:
	leal	(%rax,%rbx), %ebx
.L1:
	addq	$104, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	movl	%ebx, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L23:
	.cfi_restore_state
	movl	%ebx, %eax
	movl	12(%rsp), %edx
	movl	%ebp, %ebx
	movl	16(%rsp), %ecx
	movl	%r9d, %ebp
	addl	%eax, %esi
	jmp	.L22
	.cfi_endproc
.LFE3:
	.size	fib, .-fib
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB2:
	.cfi_startproc
.L50:
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movl	$44, %r13d
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	xorl	%ebx, %ebx
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
.L51:
	movl	%r13d, %ebp
	xorl	%r12d, %r12d
.L52:
	leal	-1(%rbp), %edi
	subl	$2, %ebp
	call	fib
	addl	%eax, %r12d
	cmpl	$1, %ebp
	jg	.L52
.L53:
	addl	%r12d, %ebx
	subl	$2, %r13d
	jne	.L51
.L54:
	addl	$1, %ebx
	movl	$1, %ebp
	movl	$10, %eax
	cmpl	$9, %ebx
	jle	.L73
	.p2align 4,,10
	.p2align 3
.L55:
	leal	(%rax,%rax,4), %eax
	addl	$1, %ebp
	addl	%eax, %eax
	cmpl	%eax, %ebx
	jge	.L55
	movl	$1, %edi
	movl	$10, %eax
	.p2align 4,,10
	.p2align 3
.L57:
	leal	(%rax,%rax,4), %eax
	addl	$1, %edi
	addl	%eax, %eax
	cmpl	%eax, %ebx
	jge	.L57
.L58:
	movslq	%edi, %rdi
	call	malloc@PLT
	movl	$1, %edi
	movq	%rax, %r12
	movl	$10, %eax
	.p2align 4,,10
	.p2align 3
.L59:
	leal	(%rax,%rax,4), %eax
	addl	$1, %edi
	addl	%eax, %eax
	cmpl	%eax, %ebx
	jge	.L59
	movslq	%edi, %rdi
.L56:
	call	malloc@PLT
	movl	$1, %edx
	movq	%rax, %rdi
	.p2align 4,,10
	.p2align 3
.L60:
	movslq	%ebx, %rax
	movl	%ebx, %ecx
	imulq	$1717986919, %rax, %rax
	sarl	$31, %ecx
	sarq	$34, %rax
	subl	%ecx, %eax
	movl	%ebx, %ecx
	leal	(%rax,%rax,4), %esi
	addl	%esi, %esi
	subl	%esi, %ecx
	movl	%ebx, %esi
	movl	%eax, %ebx
	movq	%rdx, %rax
	addl	$48, %ecx
	movb	%cl, -1(%r12,%rdx)
	addq	$1, %rdx
	cmpl	$99, %esi
	jg	.L60
.L61:
	cltq
	addl	$48, %ebx
	movslq	%ebp, %rbp
	movb	%bl, (%r12,%rax)
	addq	%rdi, %rbp
	.p2align 4,,10
	.p2align 3
.L62:
	movzbl	(%r12,%rax), %ecx
	movq	%rax, %rdx
	subq	$1, %rax
	negq	%rdx
	movb	%cl, -1(%rbp,%rdx)
	cmpl	$-1, %eax
	jne	.L62
.L63:
	xorl	%eax, %eax
	call	printf@PLT
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L73:
	.cfi_restore_state
	movl	$1, %edi
	call	malloc@PLT
	movl	$1, %edi
	movq	%rax, %r12
	jmp	.L56
	.cfi_endproc
.LFE2:
	.size	main, .-main
	.ident	"GCC: (GNU) 14.1.1 20240522"
	.section	.note.GNU-stack,"",@progbits
