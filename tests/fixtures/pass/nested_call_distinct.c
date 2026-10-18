/* PASS: nested calls of distinct owners stay disjoint. */
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
    free(y);
}

int main(void) {
    int *p = malloc(4);
    int *q = malloc(4);
    f(g(p), h(q));
    free(p);
    return 0;
}
