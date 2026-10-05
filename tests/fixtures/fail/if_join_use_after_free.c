/* FAIL: join after if must over-approximate; a free on one path taints the join. */
void *malloc(unsigned long n);
void free(void *p);

void inspect(void *p) {
}

int main(void) {
    void *p = malloc(8);
    if (1) {
        free(p);
    }
    inspect(p);
    return 0;
}
