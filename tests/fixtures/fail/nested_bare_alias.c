/* FAIL: `h(p)` frees `p` while `g(p)` reads it. Previously accepted. */
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
    f(g(p), h(p));
    return 0;
}
