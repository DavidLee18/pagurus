/* FAIL: `q = p` then the remaining owner is passed as both Never and Always. */
void *malloc(unsigned long);
void free(void *);

void f(int *a, int *b) {
    free(b);
}

int main(void) {
    int *p = malloc(4);
    int *q = p;
    f(q, q);
    return 0;
}
