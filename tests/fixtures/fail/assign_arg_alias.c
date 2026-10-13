/* FAIL: `q = malloc()` stores the fresh pointer in `q`, then `q` is consumed. */
void *malloc(unsigned long);
void free(void *);

void use(int *p) {
}

void f(int *a, int *b) {
    free(b);
    use(a);
}

int main(void) {
    int *q = malloc(4);
    f(q = malloc(4), q);
    return 0;
}
