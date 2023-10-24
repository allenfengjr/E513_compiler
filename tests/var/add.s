	.align 16
block.1:
    movq %rcx, %rdi
    callq print_int
    movq $0, %rax
    jmp conclusion

	.align 16
block.2:
    movq $42, %rcx
    jmp block.1

	.align 16
block.3:
    movq $777, %rcx
    jmp block.1

	.align 16
block.4:
    cmpq $0, %r12
    je block.2
    jmp block.3

	.align 16
block.5:
    movq $0, %rcx
    jmp block.1

	.align 16
start:
    callq read_int
    movq %rax, %r12
    movq %r12, %rax
    cmpq $1, %rax
    sete %al
    movzbq %al, %rbx
    cmpq $0, %rbx
    je block.4
    jmp block.5

	.globl main
	.align 16
main:
    pushq %rbp
    movq %rsp, %rbp
    pushq %rbx
    pushq %r12
    subq $0, %rsp
    jmp start

	.align 16
conclusion:
    addq $0, %rsp
    popq %r12
    popq %rbx
    popq %rbp
    retq 


