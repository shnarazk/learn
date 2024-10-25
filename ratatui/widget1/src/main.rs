use {
    color_eyre::eyre::{bail, WrapErr}, // owo_colors::Style, Result

    crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind},
    ratatui::{
        layout::{Direction, Layout, Rect},
        prelude::*,
        style::Color,
        symbols::border,
        widgets::{block::*, *},
    },
    std::time::{Duration, Instant},
};
mod errors;
mod tui;

#[derive(Debug)]
pub struct App {
    counter: i16,
    exit: bool,
    start: Instant,
}
impl Default for App {
    fn default() -> Self {
        App {
            counter: 0,
            exit: false,
            start: Instant::now(),
        }
    }
}

impl App {
    pub fn run(&mut self, terminal: &mut tui::Tui) -> color_eyre::Result<()> {
        while !self.exit {
            terminal.draw(|frame| self.render_frame(frame))?;
            self.handle_events().wrap_err("handle events failed")?;
        }
        Ok(())
    }
    fn render_frame(&self, frame: &mut Frame) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(5), Constraint::Min(5), Constraint::Min(5)])
            .split(frame.area());
        let d1: f64 = (self.start.elapsed().as_millis() % 10000u128) as f64 / 5000.0;
        let d2: f64 = if self.counter == 0 {
            1.0
        } else {
            (self.counter as f64 / 8.0).log2()
        };
        let v1 = (1isize..50)
            .map(|n| {
                let x = (n as f64 / 25.0) - 1.0;
                (x, ((x * d2 + d1) * 6.0).sin())
            })
            .collect::<Vec<_>>();
        let v2 = (1isize..50)
            .map(|n| {
                let x = (n as f64 / 25.0) - 1.0;
                (x, ((x * d2 + d1) * 6.0).cos())
            })
            .collect::<Vec<_>>();
        let dataset: Vec<Dataset> = vec![
            Dataset::default()
                .name("sin() wave")
                .marker(symbols::Marker::Dot)
                .style(Style::default().fg(Color::Cyan))
                .data(&v1),
            Dataset::default()
                .name("cosine() wave")
                .marker(symbols::Marker::Dot)
                .style(Style::default().fg(Color::Red))
                .data(&v2),
        ];
        let chart = self.chart(dataset);
        let bar_chart = self.bar_chart();
        frame.render_widget(chart, chunks[0]);
        frame.render_widget(bar_chart, chunks[1]);
        frame.render_widget(self, chunks[2]);
    }
    fn handle_events(&mut self) -> color_eyre::Result<()> {
        if crossterm::event::poll(Duration::from_millis(10))? {
            match event::read()? {
                Event::Key(key_event) if key_event.kind == KeyEventKind::Press => self
                    .handle_key_event(key_event)
                    .wrap_err_with(|| format!("handling key event failed:\n{key_event:#?}")),
                _ => Ok(()),
            }
        } else {
            Ok(())
        }
    }
    fn handle_key_event(&mut self, key_event: KeyEvent) -> color_eyre::Result<()> {
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
    fn decrement_counter(&mut self) -> color_eyre::Result<()> {
        if let Some(n) = self.counter.checked_sub(1) {
            self.counter = n;
            Ok(())
        } else {
            bail!("counter underflow");
        }
    }
    fn increment_counter(&mut self) -> color_eyre::Result<()> {
        if let Some(n) = self.counter.checked_add(1) {
            self.counter = n;
            Ok(())
        } else {
            bail!("counter underflow");
        }
    }
}

impl App {
    fn bar_chart(&self) -> BarChart {
        let b = vec![
            ("data0", 2),
            ("data1", 4),
            ("data2", 1),
            ("data3", self.counter.max(2) as u64),
            ("data4", 3),
            ("data5", 5),
            ("data6", 10),
            ("data7", 6),
            ("data8", 18),
            ("data9", 5),
        ];
        let barchart = BarChart::default()
            .block(Block::bordered().title("BarChart"))
            .data(&b)
            .bar_width(7)
            .bar_style(Style::default().fg(Color::Red))
            .value_style(Style::default().fg(Color::White).bg(Color::Blue));
        barchart
    }
    fn chart<'a>(&'a self, dataset: Vec<Dataset<'a>>) -> Chart<'a> {
        let x_labels = vec![
            Span::styled("-1.0", Style::default()),
            Span::styled("-0.5", Style::default()),
            Span::styled("0.0", Style::default()),
            Span::styled("0.5", Style::default()),
            Span::styled("1.0", Style::default()),
        ];
        let y_labels = vec![
            Span::styled("-2", Style::default()),
            Span::styled("-1", Style::default()),
            Span::styled("0", Style::default()),
            Span::styled("1", Style::default()),
            Span::styled("2", Style::default()),
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
                    .bounds([-1.0, 1.0]),
            )
            .y_axis(
                Axis::default()
                    .title("Y axis")
                    .style(Style::default().fg(Color::Gray))
                    .labels(y_labels)
                    .bounds([-2.0, 2.0]),
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
        let _title = Title::from(" Counter App Tutorial ".bold());
        let instructions = Line::from(vec![
            " Decrement ".into(),
            "<Left>".blue().bold(),
            " Increment ".into(),
            "<Right>".blue().bold(),
            " Quit ".into(),
            "<Q> ".blue().bold(),
        ]);
        let block = Block::default()
            .title_alignment(Alignment::Center)
            .title_bottom(instructions)
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

fn main() -> color_eyre::Result<()> {
    errors::install_hooks()?;
    let mut terminal = tui::init()?;
    App::default().run(&mut terminal)?;
    tui::restore()?;
    Ok(())
}
