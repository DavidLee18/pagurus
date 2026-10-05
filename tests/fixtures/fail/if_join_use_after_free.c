/* FAIL: join after if must still track the owner assigned on one path. */
void *malloc(unsigned long n);
void free(void *p);
void inspect(void *p);

int main(void) {
    void *p;
    if (1) {
        p = malloc(8);
    }
    free(p);
    inspect(p);
    return 0;
}
