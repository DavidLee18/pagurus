/* FAIL: `r = g(q = p)` stores `q`, then `h(q)` frees it. */
void *malloc(unsigned long);
void free(void *);

int *g(int *a) {
    return a;
}

int *h(int *b) {
    free(b);
    return 0;
}

void f(int *x, int *y) {
}

int main(void) {
    int *p = malloc(4);
    int *q = malloc(4);
    int *r = malloc(4);
    f(r = g(q = p), h(q));
    return 0;
}
