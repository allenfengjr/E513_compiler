	.globl main
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $64, %rsp
    movq $1, -32(%rbp)
    movq $42, -56(%rbp)
    movq -32(%rbp), %rax
    movq %rax, -48(%rbp)
    addq $7, -48(%rbp)
    movq -48(%rbp), %rax
    movq %rax, -8(%rbp)
    movq -48(%rbp), %rax
    movq %rax, -40(%rbp)
    movq -56(%rbp), %rax
    addq %rax, -40(%rbp)
    movq -8(%rbp), %rax
    movq %rax, -24(%rbp)
    negq -24(%rbp)
    movq -40(%rbp), %rax
    movq %rax, -16(%rbp)
    movq -24(%rbp), %rax
    addq %rax, -16(%rbp)
    movq -16(%rbp), %rdi
    callq print_int
    addq $64, %rsp
    popq %rbp
    retq 

