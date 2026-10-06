/* FAIL: Always then Never of the same owner `p` (reversed parameter order). */
void *malloc(unsigned long);
void free(void *);

void g(int *a, int *b) {
    free(a);
}

int main(void) {
    int *p = malloc(4);
    g(p, p);
    return 0;
}
