void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
char*strdup(const char*);
int main(void){char*p=strdup("x");free(p);free(p);return 0;}
