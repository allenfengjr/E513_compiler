	.globl main
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $8, %rsp
    movq %rbx, 0(%rbp)
    movq $1, %rcx
    movq $42, %rsi
    movq %rcx, %r9
    addq $7, %r9
    movq %r9, %r8
    movq %r9, %r10
    addq %rsi, %r10
    movq %r8, %rbx
    negq %rbx
    movq %r10, %rdx
    addq %rbx, %rdx
    movq %rdx, %rdi
    callq print_int
    movq 0(%rbp), %rbx
    addq $8, %rsp
    popq %rbp
    retq 

