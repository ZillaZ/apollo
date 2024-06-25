#include <alloca.h>
#include <stdio.h>
#include <stdlib.h>

int fib(int n) {
    if(n < 2) {
        return n;
    }
    return fib(n-1) + fib(n-2);
}

int main(int argc, char** argv) {
    int number = atoi(argv[1]);
    int result = fib(number);
    printf("%d\n", result);
}
