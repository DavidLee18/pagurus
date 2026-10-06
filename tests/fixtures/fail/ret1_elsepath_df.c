/* FAIL: the then-branch returns after one free; the else-path double-frees. */
void *malloc(unsigned long n);
void free(void *p);

int f(int c) {
    int *p = malloc(4);
    if (c) {
        free(p);
        return 0;
    }
    free(p);
    free(p);
    return 1;
}

int main(void) {
    return f(1);
}
