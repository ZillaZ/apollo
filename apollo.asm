	.file	"fake.c"
	.text
	.section	.rodata
.LC0:
	.string	"Hello, Raylib!"
.LC1:
	.string	"sexokkk\n"
.LC2:
	.string	"%d\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r13
	pushq	%r12
	subq	$16, %rsp
	.cfi_offset 13, -24
	.cfi_offset 12, -32
.L1:
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdx
	movl	$600, %esi
	movl	$800, %edi
	call	InitWindow@PLT
	movl	$60, %edi
	call	SetTargetFPS@PLT
	movl	$0, -20(%rbp)
	jmp	.L2
.L3:
	call	BeginDrawing@PLT
.L4:
	cmpl	$60, -20(%rbp)
	jne	.L6
	jmp	.L9
.L2:
	call	WindowShouldClose@PLT
	xorl	$1, %eax
	testb	%al, %al
	jne	.L3
.L5:
	leaq	.LC1(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, %eax
	jmp	.L10
.L9:
.L7:
	movl	-20(%rbp), %eax
	movl	%eax, %esi
	leaq	.LC2(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$0, -20(%rbp)
	jmp	.L8
.L6:
	addl	$1, -20(%rbp)
.L8:
	movq	%r12, %rdx
	movabsq	$-4294967296, %rax
	andq	%rdx, %rax
	orb	$-1, %al
	movq	%rax, %r12
	movq	%r12, %rax
	movl	%eax, %edx
	movabsq	$1095216660480, %rax
	orq	%rdx, %rax
	movq	%rax, %r12
	movq	%r13, %rdx
	movabsq	$-4294967296, %rax
	andq	%rdx, %rax
	movq	%rax, %r13
	movq	%r13, %rax
	movl	%eax, %edx
	movabsq	$1095216660480, %rax
	orq	%rdx, %rax
	movq	%rax, %r13
	movq	%r12, %rdx
	movq	%r13, %rax
	movq	%rdx, %rdi
	movq	%rax, %rsi
	call	ClearBackground@PLT
	call	EndDrawing@PLT
	jmp	.L2
.L10:
	addq	$16, %rsp
	popq	%r12
	popq	%r13
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (GNU) 14.2.1 20240910"
	.section	.note.GNU-stack,"",@progbits
