	.file	"fake.c"
	.text
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB2:
	.cfi_startproc
.L1:
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movl	$3, %edi
	call	malloc@PLT
	movb	$51, 2(%rax)
	movq	%rax, %rdi
	movl	$12849, %eax
	movw	%ax, (%rdi)
	xorl	%eax, %eax
	call	printf@PLT
	xorl	%eax, %eax
	addq	$8, %rsp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE2:
	.size	main, .-main
	.ident	"GCC: (GNU) 14.1.1 20240522"
	.section	.note.GNU-stack,"",@progbits
