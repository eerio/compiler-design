#define _GNU_SOURCE
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SHELL_COMMAND_SIZE (128 * 1024)

extern char **environ;

int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <command> [args...]\n", argv[0]);
        return 1;
    }

    // Directory to create the temporary file
    const char *dir = "/tmp";

    // Open a temporary file
    int fd = open(dir, O_TMPFILE | O_RDWR, 0600);
    if (fd < 0) {
        perror("open");
        return 1;
    }

    // Convert the file descriptor to a string
    char fd_str[16];
    snprintf(fd_str, sizeof(fd_str), "%d", fd);

    // Add the file descriptor as an environment variable
    if (setenv("TEMP_FILE_FD", fd_str, 1) < 0) {
        perror("setenv");
        close(fd);
        return 1;
    }

    // Get the current shell from the $SHELL environment variable
    char *shell = getenv("SHELL");
    if (shell == NULL) {
        fprintf(stderr, "$SHELL environment variable not set\n");
        close(fd);
        return 1;
    }

    // Prepare the arguments for execve
    // Allocate space for the shell, -c flag, command string, and NULL terminator
    char **cmd_args = malloc(4 * sizeof(char *));
    if (cmd_args == NULL) {
        perror("malloc");
        close(fd);
        return 1;
    }

    // Use the current shell as the first argument
    cmd_args[0] = shell;

    // Add the -c flag to tell the shell to execute the command string
    cmd_args[1] = "-c";

    // Combine the rest of the arguments into a single command string
    char *cmd_str = malloc(SHELL_COMMAND_SIZE);
    if (cmd_str == NULL) {
        perror("malloc");
        free(cmd_args);
        close(fd);
        return 1;
    }

    cmd_str[0] = '\0';  // Initialize as an empty string

    size_t total_len = 0;
    for (int i = 1; i < argc; i++) {
        // Check if the total length of the command string exceeds the buffer size
        size_t arg_len = strlen(argv[i]);
        if (total_len + arg_len + 1 > SHELL_COMMAND_SIZE) {
            fprintf(stderr, "Command string too long\n");
            free(cmd_args);
            free(cmd_str);
            close(fd);
            return 1;
        }

        strcat(cmd_str, argv[i]);
        if (i < argc - 1) {
            strcat(cmd_str, " "); // Add space between arguments
        }
    }

    // Set the combined command string as the argument
    cmd_args[2] = cmd_str;
    cmd_args[3] = NULL; // Null-terminate the argument list

    // Execute the shell with the -c option and the command
    execve(cmd_args[0], cmd_args, environ);

    // If execve fails
    perror("execve");
    free(cmd_args);
    free(cmd_str);
    close(fd);
    return 1;
}
