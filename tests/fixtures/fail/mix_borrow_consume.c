/* FAIL: Never then Always of the same owner `p`. */
void *malloc(unsigned long);
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *p = malloc(4);
    f(p, p);
    return 0;
}
