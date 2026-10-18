/* FAIL: `g(r = p)` stores `r`, then `r` is consumed. Previously accepted. */
void *malloc(unsigned long);
void free(void *);

int *g(int *a) {
    return a;
}

void f(int *x, int *y) {
    free(y);
}

int main(void) {
    int *p = malloc(4);
    int *r = malloc(4);
    f(g(r = p), r);
    return 0;
}
