import ReactMarkdown from 'react-markdown';
import rehypeKatex from 'rehype-katex';
import remarkGfm from 'remark-gfm';
import remarkMath from 'remark-math';
import 'katex/dist/katex.min.css';
import './css/DialoguePhone.css';

export type DialogueImageContent = {
  src: string;
  alt?: string;
  caption?: string;
  href?: string;
};

export type DialogueTextPart = {
  kind: 'text';
  text: string;
};

export type DialogueImagePart = {
  kind: 'image';
} & DialogueImageContent;

export type DialogueMessagePart =
  | DialogueTextPart
  | DialogueImagePart;

export type DialogueTextMessage<Speaker extends string = string> = {
  speaker: Speaker;
  kind?: 'text';
  text: string;
  image?: DialogueImageContent;
};

export type DialogueImageMessage<Speaker extends string = string> = {
  speaker: Speaker;
  kind: 'image';
} & DialogueImageContent;

export type DialoguePartsMessage<Speaker extends string = string> = {
  speaker: Speaker;
  kind: 'parts';
  parts: DialogueMessagePart[];
};

export type DialogueMessage<Speaker extends string = string> =
  | DialogueTextMessage<Speaker>
  | DialogueImageMessage<Speaker>
  | DialoguePartsMessage<Speaker>;

export type DialoguePhoneProps<Speaker extends string = string> = {
  title?: string;
  localSpeaker: Speaker;
  remoteSpeaker: Speaker;
  remoteAvatarSrc?: string;
  remoteAvatarAlt?: string;
  subtitle?: string;
  showSpeakerLabels?: boolean;
  messages: DialogueMessage<Speaker>[];
};

export function DialoguePhone<Speaker extends string>({
  title,
  localSpeaker,
  remoteSpeaker,
  remoteAvatarSrc,
  remoteAvatarAlt,
  subtitle,
  showSpeakerLabels = false,
  messages,
}: DialoguePhoneProps<Speaker>) {
  function renderImageCard(image: DialogueImageContent, mine: boolean) {
    const imageCard = (
      <div className="dialogue-image-card">
        <img className="dialogue-image" src={image.src} alt={image.alt ?? image.caption ?? ''} />
        {image.caption && (
          <div className={`dialogue-image-caption ${mine ? 'mine' : 'theirs'}`}>
            {image.caption}
          </div>
        )}
      </div>
    );

    if (image.href) {
      return (
        <a
          className="dialogue-image-link"
          href={image.href}
          target="_blank"
          rel="noreferrer"
        >
          {imageCard}
        </a>
      );
    }

    return imageCard;
  }

  function renderText(text: string) {
    return (
      <ReactMarkdown
        remarkPlugins={[remarkGfm, remarkMath]}
        rehypePlugins={[rehypeKatex]}
      >
        {text}
      </ReactMarkdown>
    );
  }

  function renderPart(part: DialogueMessagePart, index: number, mine: boolean) {
    if (part.kind === 'image') {
      return (
        <div className="dialogue-message-part" key={index}>
          {renderImageCard(part, mine)}
        </div>
      );
    }

    return (
      <div className="dialogue-message-part" key={index}>
        {renderText(part.text)}
      </div>
    );
  }

  function renderMessageContent(message: DialogueMessage<Speaker>, mine: boolean) {
    if (message.kind === 'image') {
      return renderImageCard(message, mine);
    }

    if (message.kind === 'parts') {
      return message.parts.map((part, index) => renderPart(part, index, mine));
    }

    return (
      <>
        {renderText(message.text)}
        {message.image && renderImageCard(message.image, mine)}
      </>
    );
  }

  return (
    <div className="dialogue-phone-widget">
      {title && <div className="dialogue-phone-title">{title}</div>}
      <div className="dialogue-phone">
        <div className="dialogue-phone-speaker" />
        <div className="dialogue-phone-screen">
          <div className="dialogue-phone-header">
            <div className={`dialogue-phone-avatar ${remoteAvatarSrc ? 'has-image' : ''}`}>
              {remoteAvatarSrc ? (
                <img
                  className="dialogue-phone-avatar-img"
                  src={remoteAvatarSrc}
                  alt={remoteAvatarAlt ?? remoteSpeaker}
                />
              ) : (
                remoteSpeaker.slice(0, 1)
              )}
            </div>
            <div>
              <div className="dialogue-phone-name">{remoteSpeaker}</div>
              {subtitle && <div className="dialogue-phone-subtitle">{subtitle}</div>}
            </div>
          </div>
          <div className="dialogue-message-list">
            {messages.map((message, index) => {
              const mine = message.speaker === localSpeaker;
              return (
                <div
                  key={index}
                  className={`dialogue-message-row ${mine ? 'mine' : 'theirs'}`}
                >
                  {showSpeakerLabels && (
                    <div className="dialogue-message-sender">{message.speaker}</div>
                  )}
                  <div
                    className={`dialogue-message-bubble ${mine ? 'mine' : 'theirs'} ${message.kind === 'image' ? 'image' : 'text'}`}
                  >
                    {renderMessageContent(message, mine)}
                  </div>
                </div>
              );
            })}
          </div>
        </div>
      </div>
    </div>
  );
}
