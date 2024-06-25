#include <alloca.h>
#include <stdio.h>
#include <stdlib.h>

char* str_conv(int number) {
    int number_len = 1;
    int copy = number;
    while(copy > 9) {
        copy /= 10;
        number_len += 1;
    }
    char* buffer = malloc(number_len);
    int index = number_len - 1;
    printf("%d\n", index);
    while(number > 0) {
        int remainder = number % 10 + 48;
        number /= 10;
        buffer[index] = (char)remainder;
        printf("%c\n", remainder);
        index -= 1;
    }
    return buffer;
}

int fib(int n) {
    if(n < 2) {
        return n;
    }
    return fib(n-1) + fib(n-2);
}

int main(int argc, char** argv) {
    int number = atoi(argv[1]);
    printf("%s\n", str_conv(number));
}
