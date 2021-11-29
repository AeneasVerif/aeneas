let _ = Easy_logging.Logging.make_logger "MainLogger" Debug [ Cli Debug ]

let log = Easy_logging.Logging.get_logger "MainLogger"
