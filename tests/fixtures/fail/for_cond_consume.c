/* FAIL: for(;cond;) evaluates cond before every iteration and on exit. */
void *malloc(unsigned long n);
void free(void *p);
int consume(int *p) { free(p); return 0; }
int main(void) {
    int *p = malloc(4);
    for (; consume(p); ) {
        p = malloc(4);
    }
    free(p);
    return 0;
}
