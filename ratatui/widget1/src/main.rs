use {
    color_eyre::{
        eyre::{bail, WrapErr},
        Result,
    },
    crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind},
    ratatui::{
        layout::{Direction, Layout, Rect},
        prelude::*,
        style::Color,
        symbols::border,
        widgets::{block::*, *},
    },
    // std::io::stdout,
};
mod errors;
mod tui;

#[derive(Debug, Default)]
pub struct App {
    counter: u8,
    exit: bool,
}

impl App {
    pub fn run(&mut self, terminal: &mut tui::Tui) -> Result<()> {
        while !self.exit {
            terminal.draw(|frame| self.render_frame(frame))?;
            self.handle_events().wrap_err("handle events failed")?;
        }
        Ok(())
    }
    fn render_frame(&self, frame: &mut Frame) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(5), Constraint::Min(5)])
            .split(frame.size());
        let dataset: Vec<Dataset> = vec![Dataset::default()
            .name("sample dataset 1")
            .marker(symbols::Marker::Dot)
            .style(Style::default().fg(Color::Cyan))
            .data(&[
                (0.0, 0.3),
                (0.2, 0.1),
                (0.3, 0.2),
                (0.4, 0.5),
                (0.6, 0.9),
                (0.8, 1.1),
            ])];
        let chart = self.chart(dataset);
        frame.render_widget(chart, chunks[0]);
        frame.render_widget(self, chunks[1]);
    }
    fn handle_events(&mut self) -> Result<()> {
        match event::read()? {
            Event::Key(key_event) if key_event.kind == KeyEventKind::Press => self
                .handle_key_event(key_event)
                .wrap_err_with(|| format!("handling key event failed:\n{key_event:#?}")),
            _ => Ok(()),
        }
    }
    fn handle_key_event(&mut self, key_event: KeyEvent) -> Result<()> {
        match key_event.code {
            KeyCode::Char('q') => self.exit(),
            KeyCode::Left => self.decrement_counter()?,
            KeyCode::Right => self.increment_counter()?,
            _ => (),
        }
        Ok(())
    }
    fn exit(&mut self) {
        self.exit = true;
    }
    fn decrement_counter(&mut self) -> Result<()> {
        if self.counter == 0 {
            bail!("counter underflow");
        }
        self.counter -= 1;
        Ok(())
    }
    fn increment_counter(&mut self) -> Result<()> {
        self.counter += 1;
        if 2 < self.counter {
            bail!("counter overflow");
        }
        Ok(())
    }
}

impl App {
    fn chart<'a>(&'a self, dataset: Vec<Dataset<'a>>) -> Chart<'a> {
        let x_labels = vec![
            Span::styled("-2", Style::default()),
            Span::styled("-1", Style::default()),
            Span::styled("0", Style::default()),
            Span::styled("1", Style::default()),
            Span::styled("2", Style::default()),
        ];
        let y_labels = vec![
            Span::styled("-1", Style::default()),
            Span::styled("0", Style::default()),
            Span::styled("1", Style::default()),
        ];
        let chart = Chart::new(dataset)
            .block(
                Block::bordered()
                    .title(" Chart 1 ".cyan().bold())
                    .title_alignment(Alignment::Center),
            )
            .x_axis(
                Axis::default()
                    .title("X axis")
                    .style(Style::default().fg(Color::Gray))
                    .labels(x_labels)
                    .bounds([-2.0, 2.0]),
            )
            .y_axis(
                Axis::default()
                    .title("Y axis")
                    .style(Style::default().fg(Color::Gray))
                    .labels(y_labels)
                    .bounds([-1.0, 1.0]),
            );
        chart
        // chart.render(area, buf);
    }
}

impl Widget for &App {
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        let title = Title::from(" Counter App Tutorial ".bold());
        let instructions = Title::from(Line::from(vec![
            " Decrement ".into(),
            "<Left>".blue().bold(),
            " Increment ".into(),
            "<Right>".blue().bold(),
            " Quit ".into(),
            "<Q> ".blue().bold(),
        ]));
        let block = Block::default()
            .title(title.alignment(Alignment::Center))
            .title(
                instructions
                    .alignment(Alignment::Center)
                    .position(Position::Bottom),
            )
            .borders(Borders::ALL)
            .border_set(border::THICK);
        let counter_text = Text::from(vec![Line::from(vec![
            "Value: ".into(),
            self.counter.to_string().yellow(),
        ])]);
        Paragraph::new(counter_text)
            .centered()
            .block(block)
            .render(area, buf);
    }
}

fn main() -> Result<()> {
    errors::install_hooks()?;
    let mut terminal = tui::init()?;
    App::default().run(&mut terminal)?;
    tui::restore()?;
    Ok(())
}
