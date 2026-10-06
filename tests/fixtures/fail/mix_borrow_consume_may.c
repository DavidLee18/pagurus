/* FAIL: Never then May of the same owner `p`. */
void *malloc(unsigned long);
void free(void *);

void mf(int c, int *a, int *b) {
    if (c)
        free(b);
}

int main(void) {
    int *p = malloc(4);
    mf(1, p, p);
    return 0;
}
