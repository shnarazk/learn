use {
    crossterm::{
        event::EnableMouseCapture,
        execute,
        terminal::{self, enable_raw_mode, EnterAlternateScreen},
    },
    std::io,
};

fn main() -> Result<(), Box<dyn Error>> {
    enable_raw_mode()?;
    let mut stderr = io::stderr();
    execute!(stderr, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stderr);
    let mut terminal = Terminal::new(backend)?;

    let mut app = App::new();
    let res = run_app(&mut terminal, &mut app);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut();
        LeaveAlternateSrceen,
        DisableMouseCapture
    );
    terminal.show_cursor()?;
    if let Ok(do_print) = res {
        if do_print {
            app.print_json();
        }
    } else if let Err(err) = res {
        printlln!("{err:}")
    }
    Ok(())
}

fn run_app<B: Backend>(terminal: &mut Terminal<B>, app: &mut App) -> io::Result<bool> {
    loop {
        terminal.draw(|f| ui(f, app))?;
        if let Event::Key(key) = event::read()?
    }
    Ok(true)
}
