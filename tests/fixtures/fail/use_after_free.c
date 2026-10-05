/* FAIL: using a pointer after free is use-after-free. */
void *malloc(unsigned long n);
void free(void *p);
void inspect(void *p);

int main(void) {
    void *p = malloc(8);
    free(p);
    inspect(p);
    return 0;
}
