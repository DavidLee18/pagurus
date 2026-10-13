/* FAIL: nested `r = (q = malloc())` stores the same pointer in `q`, then `q` is consumed. */
void *malloc(unsigned long);
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *q = malloc(4);
    int *r = malloc(4);
    f(r = (q = malloc(4)), q);
    return 0;
}
