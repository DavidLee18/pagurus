/* FAIL: callee consumes p; *p afterwards is unsupported / UAF. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p) {
    int *q = p;
    free(q);
}

int main(void) {
    int *p = malloc(4);
    w(p);
    *p = 5;
    return 0;
}
