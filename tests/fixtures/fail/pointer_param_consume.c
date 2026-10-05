/* FAIL: passing a unique owner to a consuming function is a move. */
void *malloc(unsigned long n);
void free(void *p);

void consume(void *p) {
    free(p);
}

int main(void) {
    void *p = malloc(8);
    consume(p);
    free(p);
    return 0;
}
