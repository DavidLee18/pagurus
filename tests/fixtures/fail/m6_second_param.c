/* FAIL: w frees only b, but w(p,p) still consumes p. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *a, int *b) { free(b); }

int main(void) {
    int *p = malloc(4);
    w(p, p);
    free(p);
    return 0;
}
