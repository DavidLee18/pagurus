/* FAIL: `g(p)` reads `p`, then `p` is consumed. Conservative: `g` may
   return an alias of `p`. Previously accepted. */
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
    f(g(p), p);
    return 0;
}
