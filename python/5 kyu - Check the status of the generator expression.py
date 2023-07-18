def check_generator(gen):
    if gen.gi_suspended:
        return 'Started'

    if gen.gi_frame is None:
        return 'Finished'
    
    return 'Created'
