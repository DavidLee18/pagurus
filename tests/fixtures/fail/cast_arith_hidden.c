void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){char*p=malloc(4);char*q=(char*)((char*)p+1);free(p);free(q);return 0;}
