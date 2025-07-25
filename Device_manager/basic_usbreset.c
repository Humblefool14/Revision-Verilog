#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <linux/usbdevice_fs.h>

int main(int argc, char **argv)
{
    const char *filename;
    int fd;
    
    if (argc != 2) {
        fprintf(stderr, "Usage: usbreset device-filename\n");
        return 1;
    }
    filename = argv[1];
    
    fd = open(filename, O_WRONLY);
    if (fd < 0) {
        perror("Error opening output file");
        return 1;
    }
    
    printf("Resetting USB device %s\n", filename);
    if (ioctl(fd, USBDEVFS_RESET, 0) < 0) {
        perror("Error in ioctl");
        return 1;
    }
    printf("Reset successful\n");
    
    close(fd);
    return 0;
}
