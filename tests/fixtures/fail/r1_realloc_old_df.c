/* FAIL: realloc consumes p; freeing p afterwards is use-after-move. */
void *malloc(unsigned long n);
void *realloc(void *p, unsigned long n);
void free(void *p);

int main(void) {
    int *p = malloc(4);
    int *q = realloc(p, 8);
    free(p);
    free(q);
    return 0;
}
