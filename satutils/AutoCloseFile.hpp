
#include <cstdio>

class AutoCloseFile
{
public:
    FILE *file;
    inline AutoCloseFile()
        : file(NULL)
    {
    }
    inline AutoCloseFile(FILE *f)
        : file(f)
    {
    }
    inline ~AutoCloseFile()
    {
        if (file)
            fclose(file);
    }
    AutoCloseFile(const AutoCloseFile &) = delete;
    AutoCloseFile &operator=(const AutoCloseFile &) = delete;
    inline operator FILE *()
    {
        return file;
    }
};
