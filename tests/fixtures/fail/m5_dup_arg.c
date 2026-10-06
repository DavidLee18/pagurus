/* FAIL: w(p,p) passes the same owner to two Always-consumed slots. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *a, int *b) {
    free(a);
    free(b);
}

int main(void) {
    int *p = malloc(4);
    w(p, p);
    return 0;
}
