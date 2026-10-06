/* FAIL: three parameters; the first Never and third Always share `p`. */
void *malloc(unsigned long);
void free(void *);

void t(int *a, int *b, int *c) {
    free(c);
}

int main(void) {
    int *p = malloc(4);
    int *q = malloc(4);
    t(p, q, p);
    return 0;
}
