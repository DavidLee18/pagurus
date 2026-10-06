void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int**pp=malloc(8);*pp=malloc(4);free(*pp);free(*pp);return 0;}
