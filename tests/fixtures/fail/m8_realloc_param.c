/* FAIL: realloc of the parameter consumes it; caller free is UAM. */
void *malloc(unsigned long n);
void *realloc(void *p, unsigned long n);
void free(void *p);

void w(int *p) {
    int *q = realloc(p, 8);
    free(q);
}

int main(void) {
    int *p = malloc(4);
    w(p);
    free(p);
    return 0;
}
