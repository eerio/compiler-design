#define _GNU_SOURCE
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

// there is one problem with this script:
// when you run './driver 3 echo $TEMP_FILE_FD_1', it will
// not print the file descriptor of the first temporary file
// because the shell will expand the $TEMP_FILE_FD_1 to nothing
// (this variable is not set in the shell)
// it also breaks on special characters like $, &, etc.
// we probably need to just use getline to parse the command

extern char **environ;

int main(int argc, char *argv[]) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <num_temp_files> <command> [args...]\n", argv[0]);
        return 1;
    }

    // Parse the number of temporary files to create
    int num_temp_files = atoi(argv[1]);
    if (num_temp_files <= 0) {
        fprintf(stderr, "Error: <num_temp_files> must be a positive integer\n");
        return 1;
    }

    // Directory to create temporary files
    const char *dir = "/tmp";

    // Array to hold file descriptors
    int *fds = malloc(num_temp_files * sizeof(int));
    if (fds == NULL) {
        perror("malloc");
        return 1;
    }

    // Create the temporary files and set environment variables
    for (int i = 0; i < num_temp_files; i++) {
        // Open a temporary file
        fds[i] = open(dir, O_TMPFILE | O_RDWR, 0600);
        if (fds[i] < 0) {
            perror("open");
            for (int j = 0; j < i; j++) close(fds[j]); // Close already opened files
            free(fds);
            return 1;
        }

        // Create the environment variable name
        char env_var_name[32];
        snprintf(env_var_name, sizeof(env_var_name), "TEMP_FILE_FD_%d", i + 1);

        // Convert the file descriptor to a string
        char fd_str[16];
        snprintf(fd_str, sizeof(fd_str), "%d", fds[i]);

        // Set the environment variable
        if (setenv(env_var_name, fd_str, 1) < 0) {
            perror("setenv");
            for (int j = 0; j <= i; j++) close(fds[j]); // Close all files
            free(fds);
            return 1;
        }
    }

    // Get the current shell from the $SHELL environment variable
    char *shell = getenv("SHELL");
    if (shell == NULL) {
        fprintf(stderr, "Error: $SHELL environment variable not set\n");
        for (int i = 0; i < num_temp_files; i++) close(fds[i]); // Close all files
        free(fds);
        return 1;
    }

    // Prepare arguments for execve
    char **cmd_args = malloc((argc + 2) * sizeof(char *));
    if (cmd_args == NULL) {
        perror("malloc");
        for (int i = 0; i < num_temp_files; i++) close(fds[i]); // Close all files
        free(fds);
        return 1;
    }

    // Build the argument array for the shell
    cmd_args[0] = shell;
    cmd_args[1] = "-c";
    cmd_args[2] = "$@"; // Use "$@" to pass all arguments safely
    cmd_args[3] = "--"; // Prevent issues with special arguments
    for (int i = 2; i < argc; i++) {
        cmd_args[i + 2] = argv[i];
    }
    cmd_args[argc + 2] = NULL;

    // Execute the shell with the command
    execve(shell, cmd_args, environ);

    // If execve fails
    perror("execve");
    for (int i = 0; i < num_temp_files; i++) close(fds[i]); // Close all files
    free(cmd_args);
    free(fds);
    return 1;
}
