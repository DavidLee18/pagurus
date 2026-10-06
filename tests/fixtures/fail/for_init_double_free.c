/* FAIL: for-init declarations are in scope of the (once-walked) body. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    for (void *p = malloc(8);;) {
        free(p);
        free(p);
    }
    return 0;
}
