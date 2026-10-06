/* FAIL: wrapping `int *q = p; free(q)` consumes the argument; caller free is UAM. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p) {
    int *q = p;
    free(q);
}

int main(void) {
    int *p = malloc(4);
    w(p);
    free(p);
    return 0;
}
