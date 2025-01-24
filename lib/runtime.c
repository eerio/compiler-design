#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdlib.h>

void error()
{
    fprintf(stderr, "runtime error\n");
    exit(1);
}

void printInt(int n)
{
    printf("%d\n", n);
}

void printString(char *s)
{
    if (!s) { error(); }
    printf("%s\n", s);
}

int readInt() 
{
    int n;
    if (scanf("%d\n", &n) < 0)
        error();
    
    return n;
}

char* readString() 
{
    char *lineptr = NULL;
    size_t n_buf;
    size_t n_read = getline(&lineptr, &n_buf, stdin);

    if (n_read == -1) 
        error();

    lineptr[n_read - 1] = '\0';
    return lineptr;
}

char* __internal_concat(char *str1, char *str2)
{
    if (!str1) { return str2; }
    if (!str2) { return str1; }

    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);

    size_t len = len1 + len2 + 1;

    char* res = malloc(sizeof(char) * len);
    if (!res) { error(); }
    memcpy(res, str1, len1);
    memcpy(res + len1, str2, len2);
    res[len - 1] = 0;

    return res;
}

char* __calloc(size_t n)
{
    char* res = calloc(n, sizeof(char));
    if (!res) { error(); }
    return res;
}