def help_me_exit_vim_or_i_will_miss_mid_term_due_and_fail_fp_course(keyboard):
    d = keyboard.key_down
    u = keyboard.key_up
    
    d('shift')
    d(';')
    u(';')
    u('shift')
    d('w')
    u('w')
    d('q')
    u('q')
    d('enter')
    u('enter')
