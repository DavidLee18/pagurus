void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void a(void*p);
void b(void*p){a(p);}
void a(void*p){if(p)b(p);else free(p);}
int main(void){int*p=malloc(4);a(p);free(p);return 0;}
